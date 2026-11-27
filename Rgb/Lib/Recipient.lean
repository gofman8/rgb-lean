import Rgb.Lib.ProxyCrypto

/-!
# Recipients

What a recipient id names, and a recipient of a send as the sender keeps it from `send_begin` to
`send_end` (`LocalRecipient`).

Recipient ids are `<chain prefix>:utxob:<seal>` or `<chain prefix>:wvout:<script>`; the model
writes the concealed seal or script so that it can be read back. A recipient with transport
endpoints is a proxy recipient: its invoice carries the public key of its operation key and its
expiration; one without exchanges the consignment out of band.
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

/-- A transport endpoint of a recipient (`LocalTransportEndpoint`). -/
structure LocalTransportEndpoint where
  /-- The proxy's HTTP URL (`TransportEndpoint::new` of the invoice's `rpc://` text). -/
  endpoint : String
  /-- The proxy answered `check_proxy` at `send_begin`. -/
  usable : Bool := false
  /-- The consignment was posted there. -/
  used : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A recipient after its checks (`LocalRecipient`). -/
structure LocalRecipient where
  recipientId : String
  beneficiary : Beneficiary
  assignment : Assignment
  /-- Witness output index (witness recipients). -/
  vout : Option Nat := none
  amountSat : Nat := 0
  blinding : UInt64 := 0
  /-- Empty for an out-of-band recipient. -/
  endpoints : List LocalTransportEndpoint := []
  /-- Hex public key of the recipient's operation key (proxy recipients). -/
  publicKey : Option String := none
  encryption : Encryption := .required
  invoiceExpiration : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- `proxy_ids`: the invoice id and the id of this operation's transfer to it. -/
def LocalRecipient.proxyIds (r : LocalRecipient) (senderPk : String) : String × String :=
  let iid := ProxyCrypto.invoiceId r.recipientId (r.publicKey.getD "")
  (iid, ProxyCrypto.transferId iid senderPk)

end Rgb.Lib
