import Rgb.Lib.Issue
import Rgb.Lib.ProxyClient

/-!
# Receiving

A receiver creates a receive and hands its invoice to the sender:
* **blind**: the receiver picks one of its UTXOs and gives only the concealed seal
  (`utxob:`); the UTXO keeps a slot for the payment until it is paid or fails;
* **witness**: the receiver gives a colored address; the sender creates an output
  paying it in the witness transaction, and the state is sealed to that output.

The receive is recorded as an incoming transfer waiting for its counterparty.
Without transport endpoints the consignment is exchanged out of band. With
endpoints (`rpc://` or `rpcs://`) the invoice carries the public key of a fresh
operation key and is reserved on its RGB proxies (`invoice.prepare`), through
which the consignment then comes; a reusable invoice (quota above 1) takes that
many transfers.

Recipient ids are in `Rgb.Lib.Recipient`. The invoice text here holds the data of
an rgb-lib invoice in a model form; the real `rgb:` format, its parser and its
builder are in `Rgb.Invoice`.
-/

namespace Rgb.Lib

namespace Wallet

/-- Narrow the requested assignment for the asset's schema (rgb-lib's receive rule). -/
def narrowAssignment (schema : Option AssetSchema) (a : Assignment) : Result Assignment :=
  match a, schema with
  | .any, some s => .ok s.anyAssignment
  | .any, none => .ok .any
  | a, some s => if s.supportsAssignment a then .ok a else .error .invalidAssignment
  | .fungible n, none => .ok (.fungible n)
  | _, none => .error .invalidAssignment

/-- `check_transport_endpoints`: no empty string, at most 3. -/
def checkTransportEndpoints (eps : List String) : Result Unit := do
  if eps.any (·.isEmpty) then
    throw (.invalidTransportEndpoints "transport endpoints cannot be empty strings")
  if eps.length > maxTransportEndpoints then
    throw (.invalidTransportEndpoints "library supports at max 3 transport endpoints")

/-- The proxy URL of each `rpc://` or `rpcs://` endpoint (`convert_transport_endpoints`). -/
def proxyUrls (eps : List String) : Result (List String) :=
  eps.mapM fun e => (·.endpoint) <$> TransportEndpoint.new e

/-- The invoice text: contract, schema, requested state, recipient and query. -/
def invoiceString (assetId : Option String) (schema : Option AssetSchema) (a : Assignment)
    (recipientId : String) (expiration : Nat) (pk : String) (eps : List String) : String :=
  let state := match a with
    | .fungible n | .inflationRight n => toString n
    | .linkRight | .mintRight => ""
    | _ => "~"
  let q := s!"expiry={expiration}&pk={pk}" ++ (if eps.isEmpty then "" else "&endpoints=" ++ ",".intercalate eps)
  s!"rgb:{assetId.getD "~"}/{(schema.map (reprStr ·)).getD "~"}/{state}/{recipientId}?{q}"

/-- Reserve an invoice on the proxies at `urls` (`invoice.prepare`, signed with the wallet's
authentication key for a proxy when it has one): the proxies after it and the latest expiration
plus retention grace among those that took it. A proxy that does not answer is skipped. -/
def reserveOnProxies (w : Wallet) (world : World) (urls : List String) (invoiceId : String)
    (expiration : Nat) (pk : String) (quota : Nat) : Result (World × Nat) := do
  let servers := urls.filterMap fun u => world.proxies.lookup u
  let (servers, deadline) ←
    Proxy.reserveInvoice servers invoiceId expiration pk quota w.proxyAuthKeys
  let keep (u : String) (s : Proxy.Server) : Proxy.Server := (servers.find? (·.url == u)).getD s
  return ({ world with proxies := world.proxies.map fun (u, s) => (u, keep u s) }, deadline)

/-- Create a receive (`blind_receive` when `witness = false`, else `witness_receive`), checks
in rgb-lib's order. With transport endpoints the invoice is reserved on its proxies first: a
blind receive keeps their retention deadline, and a reusable invoice (`quota > 1`) gets an
invoice row live until that deadline plus the clock skew margin. A witness receive may reuse an
address the wallet revealed, unless an earlier witness receive on it used the out-of-band
exchange. -/
def receive (w : Wallet) (world : World) (witness : Bool) (assetId : Option String)
    (assignment : Assignment) (expiration : Nat) (endpoints : List String := [])
    (minConfirmations : Nat := 1) (quota : Nat := 1) (online : Option Online := none)
    (address : Option Script := none) (encryption : Option Encryption := none) :
    Result (Wallet × World × ReceiveData) := do
  let now := world.now
  let encryption := encryption.getD .required
  let outOfBand := endpoints.isEmpty
  if quota == 0 then throw (.invalidQuota "must be at least 1")
  if outOfBand && quota > 1 then
    throw (.invalidQuota "a reusable invoice requires transport endpoints")
  if address.isSome && !witness then
    throw (.unsupportedAddressReuse "only witness receives can reuse an address")
  if address.isSome && outOfBand then
    throw (.unsupportedAddressReuse
      "a witness receive reusing an address requires transport endpoints")
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
        -- `check_reused_address`; the model takes the address's script, which always parses
        if !w.isColored a then
          throw (.cannotReuseAddress "not an address of the wallet's colored keychain")
        if !((List.range w.coloredNext).any fun i => w.coloredScript i == a) then
          throw (.cannotReuseAddress "not revealed yet")
        pure (Beneficiary.witnessVout a, RecipientTypeFull.witness none, w)
      | none =>
        let (script, w1) := w.newColoredAddress
        pure (Beneficiary.witnessVout script, RecipientTypeFull.witness none, w1)
    else
      let t ← w.getUtxo [] true (some (w.maxUtxoAllocations - quota)) (some now)
      let g := GraphSeal.ofOutpoint t.outpoint (now.toUInt64 * 7919 + t.idx.toUInt64)
      pure (Beneficiary.blindedSeal g.conceal, RecipientTypeFull.blind t.outpoint,
        { w with stock := w.stock.storeSecretSeal g }) : Result _)
  w := w'
  let recipientId := beneficiary.recipientId w.chainNet
  -- `earlier_witness_receives_to_share`: the earlier witness receives on a reused address must
  -- not use the out-of-band exchange; those not sharing their data yet are marked to share it
  let earlier := w.db.transfers.filter fun t => t.recipientId == some recipientId &&
    (w.db.batchOfAssetTransfer? t.assetTransferIdx).any (·.incoming) &&
    (match t.recipientType with | some (.witness _) => true | _ => false)
  if address.isSome && earlier.any fun t => (w.db.endpointsOf t.idx).isEmpty then
    throw (.cannotReuseAddress "an earlier witness receive on it used the out-of-band exchange")
  let toShare := if address.isSome then (earlier.filter (·.receiveDir.isNone)).map (·.idx) else []
  let schema ← match assetId with
    | some id => (w.asset? id).map (some ·.schema)
    | none => pure none
  let urls ← if outOfBand then pure [] else do
    checkTransportEndpoints endpoints
    if endpoints.eraseDups.length != endpoints.length then
      throw (.invalidTransportEndpoints "no duplicate transport endpoints allowed")
    proxyUrls endpoints
  let a ← narrowAssignment schema assignment
  if expiration < now || expiration > now + maxExpirationSecs then throw .invalidExpiration
  let (sk, w1) := w.newOperationKey now
  w := w1
  let pk := sk.pk
  let invoice := invoiceString assetId schema a recipientId expiration pk endpoints
  let (world, deadline) ← if outOfBand then pure (world, none) else do
    let iid := ProxyCrypto.invoiceId recipientId pk
    let (world, d) ← w.reserveOnProxies world urls iid expiration pk quota
    pure (world, some d)
  let invoiceDeadline := if quota > 1 then deadline.map (· + proxyClockSkewMarginSecs) else none
  let receiveDir := if quota > 1 || address.isSome then
      some s!"{recipientId.replace ":" "_"}_{(pk.take 16).toString}"
    else none
  let (bi, db) := w.db.fresh
  let (ati, db) := db.fresh
  let (ii, db) := if invoiceDeadline.isSome then db.fresh else (0, db)
  let (ti, db) := db.fresh
  let batch : DbBatchTransfer :=
    { idx := bi, status := .waitingCounterparty, createdAt := now, updatedAt := now
      expiration := some expiration, minConfirmations, incoming := true
      operationSecretKey := some sk.seed, retentionDeadline := if witness then none else deadline }
  let tr : DbTransfer :=
    { idx := ti, assetTransferIdx := ati, requestedAssignment := some a
      recipientType := some recipientType, recipientId := some recipientId
      invoiceString := some invoice, recipientPubkey := some pk, recipientEncryption := encryption
      invoiceIdx := invoiceDeadline.map fun _ => ii, receiveDir }
  let invoiceRow := invoiceDeadline.map fun d =>
    ({ idx := ii, quota, assetId, deadline := d } : DbInvoice)
  -- the earlier receives keep their data in the directory named after the recipient id
  let share (t : DbTransfer) : DbTransfer :=
    if toShare.contains t.idx then { t with receiveDir := some (recipientId.replace ":" "_") }
    else t
  let db := { db with
    batchTransfers := db.batchTransfers ++ [batch]
    assetTransfers := db.assetTransfers ++ [⟨ati, true, bi, assetId, none⟩]
    invoices := db.invoices ++ invoiceRow.toList
    transfers := db.transfers.map share ++ [tr]
    endpoints := db.endpoints ++ urls.map (⟨ti, ·, .recipientProxy, false⟩)
    pendingWitnessScripts := match beneficiary with
      | .witnessVout s => db.pendingWitnessScripts ++ [s]
      | _ => db.pendingWitnessScripts
    backupInfo := { db.backupInfo with lastOperationTimestamp := now } }
  let address := match beneficiary with
    | .witnessVout s => some (reprStr s)
    | _ => none
  return ({ w with db }, world, ⟨invoice, recipientId, expiration, bi, pk, address⟩)

/-- `blind_receive`. -/
def blindReceive (w : Wallet) (world : World) (assetId : Option String) (a : Assignment)
    (expiration : Nat) (endpoints : List String := []) (minConfirmations : Nat := 1)
    (online : Option Online := none) (encryption : Option Encryption := none) (quota : Nat := 1) :
    Result (Wallet × World × ReceiveData) :=
  w.receive world false assetId a expiration endpoints minConfirmations quota online none encryption

/-- `witness_receive`. -/
def witnessReceive (w : Wallet) (world : World) (assetId : Option String) (a : Assignment)
    (expiration : Nat) (endpoints : List String := []) (minConfirmations : Nat := 1)
    (online : Option Online := none) (encryption : Option Encryption := none) (quota : Nat := 1)
    (address : Option Script := none) : Result (Wallet × World × ReceiveData) :=
  w.receive world true assetId a expiration endpoints minConfirmations quota online address
    encryption

end Wallet

end Rgb.Lib
