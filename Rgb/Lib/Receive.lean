import Rgb.Lib.Issue

/-!
# Receiving

A receiver creates a receive and hands its invoice to the sender:
* **blind**: the receiver picks one of its UTXOs and gives only the concealed seal
  (`utxob:`); the UTXO keeps a slot for the payment until it is paid or fails;
* **witness**: the receiver gives a colored address; the sender creates an output
  paying it in the witness transaction, and the state is sealed to that output.

The receive is recorded as an incoming transfer waiting for its counterparty.
Without transport endpoints the consignment is exchanged out of band; with
endpoints it goes through RGB proxies.

Recipient ids are `<chain prefix>:utxob:<seal>` or `<chain prefix>:wvout:<script>`;
the model writes the concealed seal or script so that it can be read back. The
invoice text here holds the data of an rgb-lib invoice in a model form; the real
`rgb:` format, its parser and its builder are in `Rgb.Invoice`.
-/

namespace Rgb.Lib

/-- What a recipient id names. -/
inductive Beneficiary where
  | blindedSeal (s : SecretSeal)
  | witnessVout (s : Script)
  deriving DecidableEq, Repr, Inhabited

namespace Beneficiary

private def digestText (d : Digest) : String := d.tag ++ "|" ++ d.data

private def digestOf? (s : String) : Option Digest :=
  match s.splitOn "|" with
  | tag :: rest => if rest.isEmpty then none else some ⟨tag, "|".intercalate rest⟩
  | [] => none

/-- Recipient id of a beneficiary on a chain network. -/
def recipientId (b : Beneficiary) (net : ChainNet) : String :=
  match b with
  | .blindedSeal s => s!"{net.prefix_}:utxob:{digestText s.d}"
  | .witnessVout (.p2tr k) => s!"{net.prefix_}:wvout:T{digestText k}"
  | .witnessVout (.p2wpkh k) => s!"{net.prefix_}:wvout:W{k}"
  | .witnessVout s => s!"{net.prefix_}:wvout:O{reprStr s}"

/-- Read a recipient id back (`RecipientInfo::new`); `invalidRecipientId` when
it is not one. -/
def parse (id : String) : Result (ChainNet × Beneficiary) := do
  match id.splitOn ":" with
  | pfx :: kind :: rest =>
    let some net := ChainNet.ofPrefix? pfx | throw .invalidRecipientId
    let body := ":".intercalate rest
    if kind == "utxob" then
      match digestOf? body with
      | some d => return (net, .blindedSeal ⟨d⟩)
      | none => throw .invalidRecipientId
    else if kind == "wvout" then
      if body.startsWith "T" then
        match digestOf? (body.drop 1).toString with
        | some d => return (net, .witnessVout (.p2tr d))
        | none => throw .invalidRecipientId
      else if body.startsWith "W" then return (net, .witnessVout (.p2wpkh (body.drop 1).toString))
      else throw .invalidRecipientId
    else throw .invalidRecipientId
  | _ => throw .invalidRecipientId

end Beneficiary

/-- Operation key of a receive or send: a name; its public key is derived. -/
def operationPubkey (sk : String) : String := toString (Digest.of "ed25519:pk" [encode sk])

namespace Wallet

/-- Narrow the requested assignment for the asset's schema (rgb-lib's receive rule). -/
def narrowAssignment (schema : Option AssetSchema) (a : Assignment) : Result Assignment :=
  match a, schema with
  | .any, some s => .ok s.anyAssignment
  | .any, none => .ok .any
  | a, some s => if s.supportsAssignment a then .ok a else .error .invalidAssignment
  | .fungible n, none => .ok (.fungible n)
  | _, none => .error .invalidAssignment

/-- Transport endpoint list checks of a receive: no empty string, at most 3, no duplicates. -/
def checkReceiveEndpoints (eps : List String) : Result Unit := do
  if eps.any (·.isEmpty) then throw (.invalidTransportEndpoints "transport endpoints cannot be empty strings")
  if eps.length > maxTransportEndpoints then
    throw (.invalidTransportEndpoints "library supports at max 3 transport endpoints")
  if eps.eraseDups.length != eps.length then
    throw (.invalidTransportEndpoints "no duplicate transport endpoints allowed")

/-- The invoice text: contract, schema, requested state, recipient and query. -/
def invoiceString (assetId : Option String) (schema : Option AssetSchema) (a : Assignment)
    (recipientId : String) (expiration : Nat) (pk : String) (eps : List String) : String :=
  let state := match a with
    | .fungible n | .inflationRight n => toString n
    | .linkRight | .mintRight => ""
    | _ => "~"
  let q := s!"expiry={expiration}&pk={pk}" ++ (if eps.isEmpty then "" else "&endpoints=" ++ ",".intercalate eps)
  s!"rgb:{assetId.getD "~"}/{(schema.map (reprStr ·)).getD "~"}/{state}/{recipientId}?{q}"

/-- Create a receive (`blind_receive` when `witness = false`, else
`witness_receive`), checks in rgb-lib's order. Returns the receive data. -/
def receive (w : Wallet) (now : Nat) (witness : Bool) (assetId : Option String) (assignment : Assignment)
    (expiration : Nat) (endpoints : List String := []) (minConfirmations : Nat := 1) (quota : Nat := 1)
    (online : Option Online := none) (address : Option Script := none) : Result (Wallet × ReceiveData) := do
  let outOfBand := endpoints.isEmpty
  if quota == 0 then throw (.invalidQuota "must be at least 1")
  if outOfBand && quota > 1 then throw (.invalidQuota "a reusable invoice requires transport endpoints")
  if address.isSome && !witness then
    throw (.unsupportedAddressReuse "only witness receives can reuse an address")
  if address.isSome && outOfBand then
    throw (.unsupportedAddressReuse "address reuse requires transport endpoints")
  if !witness && quota > w.maxUtxoAllocations then
    throw (.invalidQuota s!"a blind invoice can receive at most {w.maxUtxoAllocations} transfers")
  match online with
  | some o => w.checkOnline o
  | none => if !outOfBand then throw .onlineNeeded
  let mut w := w
  let (beneficiary, recipientType, w') ← (do
    if witness then
      match address with
      | some a =>
        -- a reused address must be a colored address already handed out
        if !((List.range w.coloredNext).any fun i => w.coloredScript i == a) then
          throw (.cannotReuseAddress "not a revealed colored address of this wallet")
        pure (Beneficiary.witnessVout a, RecipientTypeFull.witness none, w)
      | none =>
        let (script, w1) := w.newColoredAddress
        pure (Beneficiary.witnessVout script, RecipientTypeFull.witness none, w1)
    else
      let t ← w.getUtxo [] true (some (w.maxUtxoAllocations - quota))
      let g := GraphSeal.ofOutpoint t.outpoint (now.toUInt64 * 7919 + t.idx.toUInt64)
      pure (Beneficiary.blindedSeal g.conceal, RecipientTypeFull.blind t.outpoint,
        { w with stock := w.stock.storeSecretSeal g }) : Result _)
  w := w'
  let recipientId := beneficiary.recipientId w.chainNet
  let schema ← match assetId with
    | some id => (w.asset? id).map (some ·.schema)
    | none => pure none
  if !outOfBand then checkReceiveEndpoints endpoints
  let a ← narrowAssignment schema assignment
  if expiration < now || expiration > now + maxExpirationSecs then throw .invalidExpiration
  let sk := s!"{w.fingerprint}/op/{now}/{w.db.next}"
  let pk := operationPubkey sk
  let invoice := invoiceString assetId schema a recipientId expiration pk endpoints
  let (bi, db) := w.db.fresh
  let (ati, db) := db.fresh
  let (ti, db) := db.fresh
  let batch : DbBatchTransfer :=
    { idx := bi, status := .waitingCounterparty, createdAt := now, updatedAt := now
      expiration := some expiration, minConfirmations, incoming := true, operationSecretKey := some sk }
  let tr : DbTransfer :=
    { idx := ti, assetTransferIdx := ati, requestedAssignment := some a, recipientType := some recipientType
      recipientId := some recipientId, invoiceString := some invoice, recipientPubkey := some pk
      recipientEncryption := .required }
  let db := { db with
    batchTransfers := db.batchTransfers ++ [batch]
    assetTransfers := db.assetTransfers ++ [⟨ati, true, bi, assetId, none⟩]
    transfers := db.transfers ++ [tr]
    endpoints := db.endpoints ++ endpoints.map (⟨ti, ·, .recipientProxy, false⟩)
    pendingWitnessScripts := match beneficiary with
      | .witnessVout s => db.pendingWitnessScripts ++ [s]
      | _ => db.pendingWitnessScripts
    backupInfo := { db.backupInfo with lastOperation := now } }
  let address := match beneficiary with
    | .witnessVout s => some (reprStr s)
    | _ => none
  return ({ w with db }, ⟨invoice, recipientId, expiration, bi, pk, address⟩)

def blindReceive (w : Wallet) (now : Nat) (assetId : Option String) (a : Assignment) (expiration : Nat)
    (endpoints : List String := []) (minConfirmations : Nat := 1) : Result (Wallet × ReceiveData) :=
  w.receive now false assetId a expiration endpoints minConfirmations

def witnessReceive (w : Wallet) (now : Nat) (assetId : Option String) (a : Assignment) (expiration : Nat)
    (endpoints : List String := []) (minConfirmations : Nat := 1) : Result (Wallet × ReceiveData) :=
  w.receive now true assetId a expiration endpoints minConfirmations

end Wallet

end Rgb.Lib
