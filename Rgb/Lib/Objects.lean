import Rgb.Lib.Enums
import Rgb.Lib.Constants
import Rgb.Stl.Types

/-!
# rgb-lib public objects

The data the wallet API takes and returns.
-/

namespace Rgb.Lib

/-- Wallet setup (`WalletData`). -/
structure WalletData where
  dataDir : String := "/data"
  bitcoinNetwork : BitcoinNetwork
  /-- At most this many allocations per UTXO; must be positive. The cap used is
  `min maxAllocationsPerUtxo 65535`. -/
  maxAllocationsPerUtxo : Nat
  /-- Schemas the wallet issues, sends and receives; must not be empty. -/
  supportedSchemas : List AssetSchema
  /-- Allow IFA and BFA on mainnet. -/
  allowRecklessSchemas : Bool := false
  /-- Always hand out vanilla address #0. -/
  addressReuseVanilla : Bool := false
  /-- Send wallet-picked colored outputs to colored address #0. -/
  addressReuseColoredAuto : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Effective allocation cap of a UTXO. -/
def WalletData.allocationCap (w : WalletData) : Nat := min w.maxAllocationsPerUtxo maxUtxoAssetAllocations

/-- Singlesig keys (`SinglesigKeys`); no mnemonic means watch-only. -/
structure SinglesigKeys where
  accountXpubVanilla : String
  accountXpubColored : String
  vanillaKeychain : Nat := keychainBtc
  masterFingerprint : String
  mnemonic : Option String := none
  witnessVersion : WitnessVersion := .taproot
  deriving DecidableEq, Repr, Inhabited

def SinglesigKeys.watchOnly (k : SinglesigKeys) : Bool := k.mnemonic.isNone

/-- Asset balance (`Balance`): amounts above `u64::MAX` are capped. -/
structure Balance where
  settled : Nat := 0
  future : Nat := 0
  spendable : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Bitcoin balance per keychain, in sats. -/
structure BtcBalance where
  vanilla : Balance
  colored : Balance
  deriving DecidableEq, Repr, Inhabited

/-- Media file, named by the hex SHA-256 of its content. -/
structure Media where
  filePath : String
  digest : String
  mime : String
  deriving DecidableEq, Repr, Inhabited

/-- An asset as `list_assets` shows it; schema-specific fields are optional. -/
structure AssetInfo where
  assetId : String
  schema : AssetSchema
  ticker : Option String
  name : String
  details : Option String
  precision : Nat
  issuedSupply : Nat
  /-- IFA: supply cap; others: the issued supply. -/
  maxSupply : Nat
  /-- IFA/BFA: last circulating supply the wallet learned. -/
  knownCirculatingSupply : Nat
  timestamp : Int
  addedAt : Int
  balance : Balance
  media : Option Media := none
  rejectList : Option RejectListLocation := none
  bridgeLocation : Option BridgeLocation := none
  linkedFromContract : Option String := none
  linkedToContract : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- What a wallet holds of one asset on one UTXO, summed (`AssignmentsCollection`). -/
structure AssignmentsCollection where
  fungible : Nat := 0
  nonFungible : Bool := false
  inflation : Nat := 0
  link : Bool := false
  mint : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace AssignmentsCollection

def add (c : AssignmentsCollection) : Assignment → AssignmentsCollection
  | .fungible n => { c with fungible := c.fungible + n.toNat }
  | .nonFungible => { c with nonFungible := true }
  | .inflationRight n => { c with inflation := c.inflation + n.toNat }
  | .linkRight => { c with link := true }
  | .mintRight => { c with mint := c.mint + 1 }
  | .any => c

def ofList (l : List Assignment) : AssignmentsCollection := l.foldl add {}

/-- `enough`: what is held covers what is needed (a UDA token must match exactly). -/
def enough (have_ need : AssignmentsCollection) : Bool :=
  have_.fungible ≥ need.fungible && have_.nonFungible == need.nonFungible &&
  have_.inflation ≥ need.inflation && (!need.link || have_.link) && have_.mint ≥ need.mint

/-- What remains after paying `need` (`change`). -/
def change (have_ need : AssignmentsCollection) : AssignmentsCollection :=
  { fungible := have_.fungible - need.fungible, nonFungible := false
    inflation := have_.inflation - need.inflation, link := false
    mint := have_.mint - need.mint }

end AssignmentsCollection

/-- Extra data of a witness recipient: the sats of its output, and the blinding
(forbidden for proxy recipients, whose blinding is derived from both keys). -/
structure WitnessData where
  amountSat : Nat
  blinding : Option UInt64 := none
  deriving DecidableEq, Repr, Inhabited

/-- One recipient of a send (`Recipient`). -/
structure Recipient where
  recipientId : String
  witnessData : Option WitnessData := none
  assignment : Assignment
  /-- Empty: the consignment is exchanged out of band. -/
  transportEndpoints : List String := []
  publicKey : Option String := none
  encryption : Encryption := .required
  expirationTimestamp : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- What a receive returns (`ReceiveData`). -/
structure ReceiveData where
  invoice : String
  recipientId : String
  expirationTimestamp : Nat
  batchTransferIdx : Nat
  publicKey : String
  address : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- A transport endpoint (`rpc://` or `rpcs://` proxy). -/
structure TransportEndpoint where
  endpoint : String
  transportType : TransportType := .jsonRpc
  deriving DecidableEq, Repr, Inhabited

/-- A transfer as `list_transfers` shows it (`Transfer`). -/
structure TransferView where
  idx : Nat
  batchTransferIdx : Nat
  createdAt : Int
  updatedAt : Int
  status : TransferStatus
  requestedAssignment : Option Assignment
  assignments : List Assignment
  kind : TransferKind
  txid : Option Txid
  recipientId : Option String
  receiveUtxo : Option Outpoint
  changeUtxos : List Outpoint
  expirationTimestamp : Option Nat
  deriving DecidableEq, Repr, Inhabited

/-- A wallet UTXO (`Utxo`). -/
structure Utxo where
  outpoint : Outpoint
  btcAmount : Nat
  /-- Colored keychain output. -/
  colorable : Bool
  /-- Its transaction is known (false for own outputs registered before broadcast). -/
  exists_ : Bool
  deriving DecidableEq, Repr, Inhabited

/-- An allocation as `list_unspents` shows it (`RgbAllocation`). -/
structure RgbAllocation where
  assetId : Option String
  assignment : Assignment
  settled : Bool
  deriving DecidableEq, Repr, Inhabited

structure Unspent where
  utxo : Utxo
  rgbAllocations : List RgbAllocation
  pendingBlinded : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An allocation the wallet tracks (`LocalRgbAllocation`). -/
structure LocalRgbAllocation where
  assetId : Option String
  assignment : Assignment
  /-- Status of the allocation's batch transfer. -/
  status : TransferStatus
  /-- The coloring puts state on the TXO (receive, issue or change). -/
  incoming : Bool
  txoSpent : Bool
  deriving DecidableEq, Repr, Inhabited

namespace LocalRgbAllocation

/-- Settled: an incoming allocation on an unspent TXO of a settled transfer, or an
outgoing one on a spent TXO whose transfer waits for confirmations. -/
def settled (a : LocalRgbAllocation) : Bool :=
  a.status != .failed &&
    ((!a.txoSpent && a.incoming && a.status == .settled) ||
      (a.txoSpent && !a.incoming && a.status == .waitingConfirmations))

/-- Future: incoming, on an unspent TXO, neither failed nor settled. -/
def future (a : LocalRgbAllocation) : Bool :=
  !a.txoSpent && a.incoming && a.status != .failed && !a.settled

/-- Held: incoming, on an unspent TXO, not failed. -/
def held (a : LocalRgbAllocation) : Bool := a.incoming && !a.txoSpent && a.status != .failed

end LocalRgbAllocation

/-- Outcome of refreshing one transfer (`RefreshedTransfer`). -/
structure RefreshedTransfer where
  updatedStatus : Option TransferStatus
  failure : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- `refresh` filter entry: a status and a direction. -/
structure RefreshFilter where
  status : RefreshTransferStatus
  incoming : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Result of an operation's `_end` (`OperationResult`). -/
structure OperationResult where
  txid : Txid
  batchTransferIdx : Nat
  entropy : UInt64
  deriving DecidableEq, Repr, Inhabited

end Rgb.Lib
