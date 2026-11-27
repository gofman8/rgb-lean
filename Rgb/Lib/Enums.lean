import Rgb.Schemas.Numbers
import Rgb.Bitcoin.Tx

/-!
# rgb-lib enums

Asset schemas and what each supports, assignments, transfer statuses and the
other enumerations of the wallet library.
-/

namespace Rgb.Lib

open Rgb.Schemas

/-- Asset schemas rgb-lib supports (`AssetSchema`, DB values 1..5). -/
inductive AssetSchema where
  | nia
  | uda
  | cfa
  | ifa
  | bfa
  deriving DecidableEq, Repr, Inhabited

namespace AssetSchema

def all : List AssetSchema := [nia, uda, cfa, ifa, bfa]

def dbValue : AssetSchema → Nat
  | nia => 1 | uda => 2 | cfa => 3 | ifa => 4 | bfa => 5

/-- Schema id as rgb-lib prints it. -/
def schemaIdString : AssetSchema → String
  | nia => "rgb:sch:RWhwUfTMpuP2Zfx1~j4nswCANGeJrYOqDcKelaMV4zU#remote-digital-pegasus"
  | uda => "rgb:sch:~6rjymf3GTE840lb5JoXm2aFwE8eWCk3mCjOf_mUztE#spider-montana-fantasy"
  | cfa => "rgb:sch:JgqK5hJX9YBT4osCV7VcW_iLTcA5csUCnLzvaKTTrNY#mars-house-friend"
  | ifa => "rgb:sch:A2n9kPNWtXUqwQJyXfY8yGHKyEPZgvrNYYYPGhXawOk#graph-salute-retro"
  | bfa => "rgb:sch:3I0xZVEQnQxYVk7vDnh5uNtQyUfsmThw6dX9n_Gvb5o#mama-swing-album"

def supportsRejectList : AssetSchema → Bool
  | ifa | bfa => true
  | _ => false

def supportsMint : AssetSchema → Bool
  | bfa => true
  | _ => false

/-- IFA and BFA are refused on mainnet. -/
def allowedOnMainnet : AssetSchema → Bool
  | nia | uda | cfa => true
  | ifa | bfa => false

def supportsInflation : AssetSchema → Bool
  | ifa => true
  | _ => false

def supportsBurn : AssetSchema → Bool
  | ifa | bfa => true
  | _ => false

def supportsLink : AssetSchema → Bool
  | ifa | bfa => true
  | _ => false

def isFungible : AssetSchema → Bool
  | uda => false
  | _ => true

end AssetSchema

/-- What an allocation holds or a request asks for (`Assignment`). -/
inductive Assignment where
  /-- A fungible amount in raw units. -/
  | fungible (amount : UInt64)
  /-- The UDA token. -/
  | nonFungible
  /-- IFA inflation allowance. -/
  | inflationRight (amount : UInt64)
  /-- Right to link the contract once to another contract. -/
  | linkRight
  /-- BFA right to mint. -/
  | mintRight
  /-- Request placeholder: any assignment the schema supports. -/
  | any
  deriving DecidableEq, Repr, Inhabited

namespace Assignment

def mainAmount : Assignment → Nat
  | fungible n => n.toNat
  | nonFungible => 1
  | _ => 0

def inflationAmount : Assignment → Nat
  | inflationRight n => n.toNat
  | _ => 0

/-- Name of the owned state type that holds the assignment. -/
def stateName? : Assignment → Option String
  | fungible _ | nonFungible => some "assetOwner"
  | inflationRight _ => some "inflationAllowance"
  | linkRight => some "linkRight"
  | mintRight => some "mintRight"
  | any => none

/-- The assignment type number that holds it. -/
def assignmentType? : Assignment → Option AssignmentType
  | fungible _ | nonFungible => some osAsset
  | inflationRight _ => some osInflation
  | linkRight => some osLink
  | mintRight => some osMint
  | any => none

def isFungible : Assignment → Bool
  | fungible _ => true
  | _ => false

end Assignment

/-- Assignments each schema supports (`supports_assignment`). -/
def AssetSchema.supportsAssignment : AssetSchema → Assignment → Bool
  | s, .fungible _ => s != .uda
  | s, .nonFungible => s == .uda
  | s, .inflationRight _ => s == .ifa
  | s, .linkRight => s == .ifa || s == .bfa
  | s, .mintRight => s == .bfa
  | _, .any => false

/-- What `Any` narrows to for each schema (`any_assignment`). -/
def AssetSchema.anyAssignment : AssetSchema → Assignment
  | .nia | .cfa => .fungible 0
  | .uda => .nonFungible
  | .ifa | .bfa => .any

/-- Main transition kinds of wallet operations (`TypeOfTransition`). -/
inductive TypeOfTransition where
  | inflate
  | transfer
  | burn
  | link
  | transferInflation
  | transferLink
  | mint
  | propagate
  deriving DecidableEq, Repr, Inhabited

def TypeOfTransition.transitionType : TypeOfTransition → TransitionType
  | .inflate => tsInflation | .transfer => tsTransfer | .burn => tsBurn | .link => tsLink
  | .transferInflation => tsTransferInflation | .transferLink => tsTransferLink
  | .mint => tsMint | .propagate => tsPropagate

/-- Status of a transfer (`TransferStatus`; DB values in comments). -/
inductive TransferStatus where
  /-- Outgoing operation saved by a non-dry-run `_begin` (5). -/
  | initiated
  /-- Receive created, or send waiting for the recipients' ACK (1). -/
  | waitingCounterparty
  /-- Received consignment has history above the safe height (6). -/
  | waitingSafeHeight
  /-- Incoming transfer ACKed, its transaction not seen yet (7). -/
  | waitingBroadcast
  /-- Transaction broadcast, waiting for enough confirmations (2). -/
  | waitingConfirmations
  /-- Final: done (3). -/
  | settled
  /-- Final: failed (4). -/
  | failed
  deriving DecidableEq, Repr, Inhabited

namespace TransferStatus

def dbValue : TransferStatus → Nat
  | waitingCounterparty => 1 | waitingConfirmations => 2 | settled => 3 | failed => 4
  | initiated => 5 | waitingSafeHeight => 6 | waitingBroadcast => 7

def isPending : TransferStatus → Bool
  | initiated | waitingCounterparty | waitingSafeHeight | waitingConfirmations
  | waitingBroadcast => true
  | _ => false

def isWaiting (s : TransferStatus) : Bool := s.isPending && s != initiated

def isFinal (s : TransferStatus) : Bool := s == settled || s == failed

/-- Statuses `fail_transfers` may move to `failed`. -/
def isFallible : TransferStatus → Bool
  | initiated | waitingCounterparty | waitingSafeHeight | waitingBroadcast => true
  | _ => false

end TransferStatus

/-- How a coloring row relates a TXO to a transfer (`ColoringType`). -/
inductive ColoringType where
  | receive
  | issue
  | input
  | change
  deriving DecidableEq, Repr, Inhabited

/-- Colorings that put an allocation on a TXO; `input` spends one. -/
def ColoringType.isIncoming : ColoringType → Bool
  | .receive | .change | .issue => true
  | .input => false

/-- How a receiver gets assets (`RecipientType`). -/
inductive RecipientType where
  /-- On an existing UTXO of the receiver, hidden behind a concealed seal. -/
  | blind
  /-- On an output of the sender's witness transaction, paid to the receiver's address. -/
  | witness
  deriving DecidableEq, Repr, Inhabited

/-- Stored receive data (`RecipientTypeFull`); a witness vout is known once paid. -/
inductive RecipientTypeFull where
  | blind (unblindedUtxo : Outpoint)
  | witness (vout : Option UInt32)
  deriving DecidableEq, Repr, Inhabited

/-- Only transport: JSON-RPC proxies (`TransportType`). -/
inductive TransportType where
  | jsonRpc
  deriving DecidableEq, Repr, Inhabited

/-- Role of a transport endpoint for a transfer. -/
inductive TransportEndpointKind where
  | recipientProxy
  | senderProxy
  deriving DecidableEq, Repr, Inhabited

/-- Consignment encryption a recipient asks for (`Encryption`). -/
inductive Encryption where
  | required
  | unsupported
  | optional
  deriving DecidableEq, Repr, Inhabited

/-- Kind of a vanilla wallet transaction. -/
inductive WalletTransactionType where
  | createUtxos
  | drain
  | sendBtc
  deriving DecidableEq, Repr, Inhabited

/-- Singlesig script kind: BIP84 `wpkh` or BIP86 `tr` (default). -/
inductive WitnessVersion where
  | segwitV0
  | taproot
  deriving DecidableEq, Repr, Inhabited

def WitnessVersion.purpose : WitnessVersion → Nat
  | .segwitV0 => 84
  | .taproot => 86

def WitnessVersion.descriptorFn : WitnessVersion → String
  | .segwitV0 => "wpkh"
  | .taproot => "tr"

/-- `list_transfers` asset filter. -/
inductive AssetFilter where
  | anyOrNone
  | none
  | id (assetId : String)
  deriving DecidableEq, Repr, Inhabited

/-- `list_transfers` scope. -/
inductive TransferScope where
  | all
  | txid (t : String)
  | batchTransfer (idx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- What a transfer is, as `list_transfers` shows it (`TransferKind`). -/
inductive TransferKind where
  | issuance
  | receiveBlind
  | receiveWitness
  | send
  | inflation
  | burn
  | link
  | mint
  deriving DecidableEq, Repr, Inhabited

/-- `list_transactions` classification. -/
inductive TransactionType where
  | rgbSend
  | drain
  | createUtxos
  | sendBtc
  | incoming
  deriving DecidableEq, Repr, Inhabited

/-- Statuses `refresh` may filter on: the waiting ones. -/
inductive RefreshTransferStatus where
  | waitingCounterparty
  | waitingSafeHeight
  | waitingBroadcast
  | waitingConfirmations
  deriving DecidableEq, Repr, Inhabited

def RefreshTransferStatus.ofStatus? : TransferStatus → Option RefreshTransferStatus
  | .waitingCounterparty => some .waitingCounterparty
  | .waitingSafeHeight => some .waitingSafeHeight
  | .waitingBroadcast => some .waitingBroadcast
  | .waitingConfirmations => some .waitingConfirmations
  | _ => none

def RefreshTransferStatus.toStatus : RefreshTransferStatus → TransferStatus
  | .waitingCounterparty => .waitingCounterparty
  | .waitingSafeHeight => .waitingSafeHeight
  | .waitingBroadcast => .waitingBroadcast
  | .waitingConfirmations => .waitingConfirmations

/-- Where moved or changed allocations go. -/
inductive ChangeDestination where
  | btcChange
  | utxo (o : Outpoint)
  deriving DecidableEq, Repr, Inhabited

end Rgb.Lib
