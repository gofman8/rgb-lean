import Rgb.Lib.Enums

/-!
# Transfer status machine

Every status change rgb-lib can make to a batch transfer, as data: the side
(incoming = receiver, outgoing = sender), the status before (none: the transfer
is created), what triggers it, its guard in words, and the status after.
`refresh` drives most changes; API calls create transfers or move them.
`fail_transfers` first refreshes the transfer it is asked to fail, so it also
takes the `refresh` edges. Settled and failed are final.
-/

namespace Rgb.Lib

/-- What moves a transfer. -/
inductive Trigger where
  | issue
  | receive
  | sendBegin
  | sendEnd
  | operationEnd
  | mintBegin
  | mintEnd
  | refresh
  | outOfBand
  | failTransfers
  deriving DecidableEq, Repr, Inhabited

structure Edge where
  incoming : Bool
  src : Option TransferStatus
  trigger : Trigger
  guard : String
  dst : TransferStatus
  deriving DecidableEq, Repr, Inhabited

open TransferStatus Trigger in
/-- The receiver's side. -/
def incomingEdges : List Edge :=
  [ ⟨true, none, issue, "an issuance is settled at once", settled⟩
  , ⟨true, none, receive, "blind or witness receive created", waitingCounterparty⟩
  , ⟨true, none, refresh, "a later transfer to a reusable invoice discovered", waitingCounterparty⟩
  , ⟨true, some waitingCounterparty, refresh, "legacy transfer, or the hub failed it", failed⟩
  , ⟨true, some waitingCounterparty, refresh, "download not decryptable or hash mismatch", failed⟩
  , ⟨true, some waitingCounterparty, refresh, "a refusal of the received consignment", failed⟩
  , ⟨true, some waitingCounterparty, outOfBand, "a refusal of the received consignment", failed⟩
  , ⟨true, some waitingCounterparty, refresh, "valid, with unsafe history", waitingSafeHeight⟩
  , ⟨true, some waitingCounterparty, outOfBand, "valid, with unsafe history", waitingSafeHeight⟩
  , ⟨true, some waitingCounterparty, refresh, "sender proxy retention grace under a day (NACK)", failed⟩
  , ⟨true, some waitingCounterparty, refresh, "proxy ACK refused: a NACK is recorded", failed⟩
  , ⟨true, some waitingCounterparty, refresh, "mint received through a proxy: own ACK", waitingBroadcast⟩
  , ⟨true, some waitingCounterparty, refresh, "a received mint whose bridge lock expired",
      failed⟩
  , ⟨true, some waitingCounterparty, refresh, "ACK posted, transaction released or donation", waitingConfirmations⟩
  , ⟨true, some waitingCounterparty, refresh, "ACK posted, no transaction yet", waitingBroadcast⟩
  , ⟨true, some waitingCounterparty, outOfBand, "out of band, donation transaction", waitingConfirmations⟩
  , ⟨true, some waitingCounterparty, outOfBand, "out of band, no donation transaction", waitingBroadcast⟩
  , ⟨true, some waitingSafeHeight, refresh, "unsafe witnesses now safe, then as from waiting counterparty",
      waitingConfirmations⟩
  , ⟨true, some waitingSafeHeight, refresh, "unsafe witnesses now safe, no transaction yet", waitingBroadcast⟩
  , ⟨true, some waitingSafeHeight, refresh, "legacy transfer and its transaction unknown", failed⟩
  , ⟨true, some waitingSafeHeight, refresh, "sender proxy retention grace under a day (NACK)",
      failed⟩
  , ⟨true, some waitingSafeHeight, refresh, "proxy ACK refused: a NACK is recorded", failed⟩
  , ⟨true, some waitingBroadcast, refresh, "transaction seen with too few confirmations", waitingConfirmations⟩
  , ⟨true, some waitingBroadcast, refresh, "enough confirmations", settled⟩
  , ⟨true, some waitingBroadcast, refresh, "broadcast deadline + a day passed, or operation expired", failed⟩
  , ⟨true, some waitingBroadcast, refresh, "released transaction received and broadcast", waitingConfirmations⟩
  , ⟨true, some waitingBroadcast, refresh, "legacy transfer past its expiration", failed⟩
  , ⟨true, some waitingBroadcast, refresh, "a checked mint whose inputs are spent elsewhere",
      failed⟩
  , ⟨true, some waitingConfirmations, refresh, "enough confirmations", settled⟩
  , ⟨true, some waitingConfirmations, refresh, "broadcast deadline + a day passed while unconfirmed", failed⟩
  , ⟨true, some waitingCounterparty, failTransfers, "expired and not downloadable any more", failed⟩
  , ⟨true, some waitingSafeHeight, failTransfers, "expired", failed⟩
  , ⟨true, some waitingBroadcast, failTransfers, "the incoming deadline passed", failed⟩ ]

open TransferStatus Trigger in
/-- The sender's side. -/
def outgoingEdges : List Edge :=
  [ ⟨false, none, sendBegin, "a non-dry-run begin", initiated⟩
  , ⟨false, none, mintBegin, "a mint, saved before signing, its consignment posted", initiated⟩
  , ⟨false, none, sendEnd, "a donation after a dry-run begin", waitingConfirmations⟩
  , ⟨false, none, sendEnd, "a transfer after a dry-run begin", waitingCounterparty⟩
  , ⟨false, some initiated, sendEnd, "donation: broadcast", waitingConfirmations⟩
  , ⟨false, some initiated, sendEnd, "transfer: wait for the ACKs", waitingCounterparty⟩
  , ⟨false, some initiated, operationEnd, "inflate, burn or link: broadcast", waitingConfirmations⟩
  , ⟨false, some initiated, mintEnd, "the bridge lock is confirmed", waitingConfirmations⟩
  , ⟨false, some initiated, mintEnd, "the bridge lock can never be confirmed", failed⟩
  , ⟨false, some initiated, failTransfers, "explicit index, signed transaction revoked", failed⟩
  , ⟨false, some initiated, failTransfers, "a sent mint whose bridge lock expired", failed⟩
  , ⟨false, some waitingCounterparty, sendEnd, "ending again before any ACK", waitingCounterparty⟩
  , ⟨false, some waitingCounterparty, refresh, "legacy transfer", failed⟩
  , ⟨false, some waitingCounterparty, refresh, "a recipient NACKed", failed⟩
  , ⟨false, some waitingCounterparty, outOfBand, "a recipient NACKed", failed⟩
  , ⟨false, some waitingCounterparty, refresh, "all ACKed, not released, operation expired", failed⟩
  , ⟨false, some waitingCounterparty, outOfBand, "all ACKed, not released, operation expired", failed⟩
  , ⟨false, some waitingCounterparty, refresh, "all ACKed: broadcast", waitingConfirmations⟩
  , ⟨false, some waitingCounterparty, outOfBand, "all ACKed: broadcast", waitingConfirmations⟩
  , ⟨false, some waitingCounterparty, refresh, "released, invoice expired, inputs spent elsewhere", failed⟩
  , ⟨false, some waitingCounterparty, refresh, "released, invoice expired, transaction on chain",
      waitingConfirmations⟩
  , ⟨false, some waitingCounterparty, refresh, "proxy lost the operation or forged an ACK: transaction known",
      waitingConfirmations⟩
  , ⟨false, some waitingCounterparty, refresh, "proxy lost the operation or forged an ACK: deadline passed",
      failed⟩
  , ⟨false, some waitingCounterparty, failTransfers, "no ACK yet and the transaction revoked", failed⟩
  , ⟨false, some waitingCounterparty, failTransfers, "its transaction is on chain: broadcast",
      waitingConfirmations⟩
  , ⟨false, some waitingConfirmations, refresh, "enough confirmations", settled⟩ ]

def edges : List Edge := incomingEdges ++ outgoingEdges

/-- A status change rgb-lib can make. -/
def canStep (incoming : Bool) (src : Option TransferStatus) (dst : TransferStatus) : Bool :=
  edges.any fun e => e.incoming == incoming && e.src == src && e.dst == dst

/-- A sequence of statuses of one transfer, from its creation. -/
def validPath (incoming : Bool) : List TransferStatus → Bool
  | [] => true
  | s :: rest =>
    let rec go (prev : TransferStatus) : List TransferStatus → Bool
      | [] => true
      | t :: rest => canStep incoming (some prev) t && go t rest
    canStep incoming none s && go s rest

/-- Final statuses have no way out. -/
theorem final_no_exit : edges.all (fun e => e.src != some .settled && e.src != some .failed) = true := by
  decide

/-- Only the sender's side has `initiated`. -/
theorem initiated_outgoing_only : edges.all (fun e => e.dst == .initiated → !e.incoming) = true := by
  decide

/-- `initiated` is never refreshed: only an `_end` or `fail_transfers` moves it. -/
theorem initiated_not_refreshed :
    edges.all (fun e => e.src == some .initiated → e.trigger != .refresh) = true := by
  decide

/-- Settlement happens only by `refresh`, from a status that saw the transaction. -/
theorem settled_by_refresh :
    edges.all (fun e => e.dst == .settled && e.src.isSome →
      e.trigger == .refresh &&
      (e.src == some .waitingConfirmations || e.src == some .waitingBroadcast)) = true := by
  decide

/-- `fail_transfers` never fails a transfer waiting for confirmations. -/
theorem fail_not_waiting_confirmations :
    edges.all (fun e => e.trigger == .failTransfers → e.src != some .waitingConfirmations) = true := by
  decide

/-- The statuses `fail_transfers` acts on are exactly the fallible ones. -/
theorem fail_only_fallible :
    edges.all (fun e => e.trigger == .failTransfers → (e.src.map TransferStatus.isFallible).getD false) = true := by
  decide

end Rgb.Lib
