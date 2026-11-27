import Rgb.Core.Collections

/-!
# Bitcoin transactions

The part of Bitcoin that RGB uses: outpoints, outputs, transactions and their
ids. Scripts are kept only as far as RGB reads them: key-path outputs of the
wallet, taproot output keys (which may carry a tapret commitment) and
`OP_RETURN` outputs (which may carry an opret commitment).
-/

namespace Rgb

/-- Satoshi amounts. -/
abbrev Sats := UInt64

/-- A Bitcoin transaction id. -/
structure Txid where
  d : Digest
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : ToString Txid := ⟨fun t => toString t.d⟩
instance : Encode Txid := ⟨fun t => encode t.d⟩

/-- A transaction output reference. -/
structure Outpoint where
  txid : Txid
  vout : UInt32
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : ToString Outpoint := ⟨fun o => s!"{o.txid}:{o.vout}"⟩
instance : Encode Outpoint := ⟨fun o => encField (encode o.txid ++ encode o.vout)⟩

/-- Output scripts, as far as RGB reads them. -/
inductive Script where
  /-- Segwit v0 key hash output of a wallet key (`wpkh`). -/
  | p2wpkh (key : String)
  /-- Segwit v0 script hash output (`wsh`), used by multisig wallets. -/
  | p2wsh (script : String)
  /-- Taproot output; `outputKey` is the tweaked key that appears on chain. -/
  | p2tr (outputKey : Digest)
  /-- `OP_RETURN` output; `data` is the pushed payload, if any. -/
  | opReturn (data : Option Digest)
  /-- Any other script (an external address). -/
  | other (s : String)
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : Encode Script := ⟨fun
  | .p2wpkh k => "W" ++ encode k
  | .p2wsh s => "H" ++ encode s
  | .p2tr k => "T" ++ encode k
  | .opReturn d => "R" ++ encode d
  | .other s => "O" ++ encode s⟩

def Script.isOpReturn : Script → Bool
  | .opReturn _ => true
  | _ => false

def Script.isTaproot : Script → Bool
  | .p2tr _ => true
  | _ => false

structure TxIn where
  prevout : Outpoint
  sequence : UInt32 := 0xFFFFFFFD
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

structure TxOut where
  value : Sats
  script : Script
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : Encode TxIn := ⟨fun i => encField (encode i.prevout ++ encode i.sequence)⟩
instance : Encode TxOut := ⟨fun o => encField (encode o.value ++ encode o.script)⟩

structure Tx where
  version : UInt32 := 2
  inputs : List TxIn
  outputs : List TxOut
  lockTime : UInt32 := 0
  deriving DecidableEq, Hashable, Inhabited, Repr

instance : Encode Tx :=
  ⟨fun t => encField (encode t.version ++ encode t.inputs ++ encode t.outputs ++ encode t.lockTime)⟩

namespace Tx

def txid (tx : Tx) : Txid := ⟨Digest.of Tag.txid [encode tx]⟩

def outpoint (tx : Tx) (vout : Nat) : Outpoint := ⟨tx.txid, vout.toUInt32⟩

def spends (tx : Tx) (o : Outpoint) : Bool := tx.inputs.any (·.prevout == o)

def outputAt? (tx : Tx) (vout : UInt32) : Option TxOut := tx.outputs[vout.toNat]?

def totalOut (tx : Tx) : Nat := (tx.outputs.map (·.value.toNat)).sum

/-- Two transactions conflict when they spend a common outpoint. -/
def conflicts (a b : Tx) : Bool := a.inputs.any fun i => b.spends i.prevout

end Tx

/-- Bitcoin networks supported by rgb-lib (`BitcoinNetwork`). -/
inductive BitcoinNetwork where
  | mainnet
  | testnet
  | testnet4
  | signet
  | regtest
  | signetCustom
  deriving DecidableEq, Repr, Inhabited

/-- The layer 1 an RGB contract lives on. -/
inductive Layer1 where
  | bitcoin
  | liquid
  deriving DecidableEq, Repr, Inhabited

/-- Chain and network a contract is bound to (`ChainNet`, wire values 0..7). -/
inductive ChainNet where
  | bitcoinMainnet
  | bitcoinTestnet3
  | bitcoinTestnet4
  | bitcoinSignet
  | bitcoinRegtest
  | liquidMainnet
  | liquidTestnet
  | bitcoinSignetCustom
  deriving DecidableEq, Repr, Inhabited

namespace ChainNet

/-- Wire value of the chain net. -/
def code : ChainNet → Nat
  | bitcoinMainnet => 0 | bitcoinTestnet3 => 1 | bitcoinTestnet4 => 2 | bitcoinSignet => 3
  | bitcoinRegtest => 4 | liquidMainnet => 5 | liquidTestnet => 6 | bitcoinSignetCustom => 7

/-- Invoice and display prefix. -/
def prefix_ : ChainNet → String
  | bitcoinMainnet => "bc" | bitcoinTestnet3 => "tb3" | bitcoinTestnet4 => "tb4"
  | bitcoinRegtest => "bcrt" | bitcoinSignet => "sb" | bitcoinSignetCustom => "sbc"
  | liquidMainnet => "lq" | liquidTestnet => "tl"

def all : List ChainNet :=
  [bitcoinMainnet, bitcoinTestnet3, bitcoinTestnet4, bitcoinSignet, bitcoinRegtest,
    liquidMainnet, liquidTestnet, bitcoinSignetCustom]

/-- Parse a prefix, ignoring case (`ChainNet::from_str`). -/
def ofPrefix? (s : String) : Option ChainNet := all.find? (·.prefix_ == s.toLower)

def layer1 : ChainNet → Layer1
  | liquidMainnet | liquidTestnet => .liquid
  | _ => .bitcoin

/-- Default signet and custom signet share the signet chain hash. -/
def chainHashName : ChainNet → String
  | bitcoinMainnet => "bitcoin" | bitcoinTestnet3 => "testnet3" | bitcoinTestnet4 => "testnet4"
  | bitcoinSignet | bitcoinSignetCustom => "signet" | bitcoinRegtest => "regtest"
  | liquidMainnet => "liquid" | liquidTestnet => "liquid-testnet"

instance : Encode ChainNet := ⟨fun c => encode c.code⟩

end ChainNet

/-- The chain net rgb-lib binds to each Bitcoin network. -/
def BitcoinNetwork.chainNet : BitcoinNetwork → ChainNet
  | .mainnet => .bitcoinMainnet
  | .testnet => .bitcoinTestnet3
  | .testnet4 => .bitcoinTestnet4
  | .signet => .bitcoinSignet
  | .regtest => .bitcoinRegtest
  | .signetCustom => .bitcoinSignetCustom

/-- Unix time of the first block of each layer 1 (`Layer1::genesis_timestamp`). -/
def Layer1.genesisTimestamp : Layer1 → Int
  | .bitcoin => 1231006505
  | .liquid => 1296692202

end Rgb
