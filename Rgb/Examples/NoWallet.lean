import Rgb.Lib.NoWallet

/-!
# No-wallet API scenarios

An issuer holds a NIA asset and sends 600 of its 1000 units to a receiver's concealed seal.
A BFA asset mints 500 units against a lock on an EVM bridge (chain 1), which has to be
included before bridge block 30. The checks run the no-wallet API on these consignments:
mint lock statuses, claims, safe heights, reject lists, inspection and SPV proofs.
-/

namespace Rgb.Examples.NoWalletScenario

open Rgb Rgb.Schemas Rgb.Lib Rgb.Lib.Evm Rgb.Lib.NoWallet

/-! ## Support -/

def fundA : Chain × Outpoint := Chain.fund {} (.p2wpkh "issuer") 10000 0
def fundB : Chain × Outpoint := fundA.1.fund (.p2wpkh "receiver") 1000 1
def chain0 : Chain := fundB.1
def utxoA : Outpoint := fundA.2
def utxoB : Outpoint := fundB.2

def terms : ContractTerms := ⟨⟨"terms"⟩, none⟩
def opts : ValidationOptions := { bitcoinNetwork := .regtest }

/-- A witness bundle of one contract's transitions, spending `spend` (entropy 5). -/
def witnessOf (cid : ContractId) (spend : List Outpoint) (ts : List Transition) : WitnessBundle :=
  let tx := mkTx spend [⟨0, .opReturn none⟩, ⟨546, .p2wpkh "issuer"⟩, ⟨9000, .p2wpkh "change"⟩]
  ((commitBundles tx [(cid, TransitionBundle.ofTransitions ts)] 5).toOption.bind
    (·.witnessBundle? cid)).getD default

/-- No EVM node and no web server answer. -/
def noNet : EvmNet := fun _ => EvmNode.unreachable
def noWeb : Web := fun _ => .error "error sending request"

/-! ## A NIA transfer -/

def spec : AssetSpec := ⟨⟨"USDT"⟩, ⟨"Tether USD"⟩, none, .centiMicro⟩

def niaGenesis : Genesis :=
  { schemaId := nia.schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList
      [ (gsNominal, [⟨.assetSpec spec⟩]), (gsTerms, [⟨.contractTerms terms⟩])
      , (gsIssuedSupply, [⟨.amount 1000⟩]) ]
    assignments := OrdMap.ofList
      [(osAsset, .fungible [(.revealed ⟨utxoA.txid, utxoA.vout, 1⟩, ⟨1000⟩)])] }

def niaCid : ContractId := niaGenesis.contractId
def bobSeal : GraphSeal := GraphSeal.ofOutpoint utxoB 42

def niaTransfer : Transition :=
  { contractId := niaCid, transitionType := tsTransfer, inputs := [⟨niaGenesis.id, osAsset, 0⟩]
    assignments := OrdMap.ofList [(osAsset, .fungible
      [(.concealed bobSeal.conceal, ⟨600⟩), (.revealed (GraphSeal.witnessVout 1 7), ⟨400⟩)])] }

def niaW : WitnessBundle := witnessOf niaCid [utxoA] [niaTransfer]
def niaConsignment : Consignment := { transfer := true, genesis := niaGenesis, bundles := [niaW] }
def niaFile : ConsignmentFile := .transfer niaConsignment
def niaTxid : String := toString niaW.witnessId

/-- A genesis of the PFA schema, which rgb-lib does not support. -/
def pfaGenesis : Genesis := { niaGenesis with schemaId := pfa.schemaId }

/-- The receiver validates before the witness is broadcast, taking it from the consignment. -/
def offchain : ValidationOptions := { opts with offchainTxid := some niaTxid }

def validateNia (o : ValidationOptions) (file : ConsignmentFile := niaFile) :=
  validateConsignmentWithResolver "nia.rgb" file (chain0.resolver .bitcoinRegtest) none none
    none o

-- a valid NIA transfer, its witness taken from the consignment as tentative
#guard (validateNia offchain).map (fun v => (v.isTransfer, v.assetSchema, v.witnesses, v.warnings))
  == .ok (true, .nia, [⟨niaTxid, .tentative, true⟩], [])
-- a TXID text reads in either case
#guard (validateNia { opts with offchainTxid := some niaTxid.toUpper }) matches .ok _
-- an offchain TXID that is no witness of the consignment
#guard validateNia { opts with offchainTxid := some (toString utxoA.txid) }
  == .error (.offchainTxidNotFound (toString utxoA.txid))
-- a contract consignment has no witness, so any offchain TXID is refused
#guard validateNia offchain (.contract { niaConsignment with transfer := false, bundles := [] })
  == .error (.offchainTxidNotFound niaTxid)
-- a text that is not a TXID is refused before the file is read
#guard validateNia { opts with offchainTxid := some "not-a-txid" } .other == .error .invalidTxid
-- the path must exist, and hold a transfer or contract consignment
#guard validateNia offchain .missing == .error (.invalidFilePath "nia.rgb")
#guard validateNia offchain (.validated true niaConsignment) == .error .invalidConsignment
-- without the offchain TXID an unbroadcast witness is unknown: the consignment is invalid
#guard validateNia opts matches .error (.consignmentValidationFailed _)
-- the consignment is validated against the requested network
#guard validateNia { offchain with bitcoinNetwork := .mainnet } == .error
  (.consignmentValidationFailed (reprStr (Failure.contractChainNetMismatch .bitcoinMainnet)))
-- rgb-lib does not know the PFA schema
#guard validateNia opts (.contract { transfer := false, genesis := pfaGenesis })
  == .error (.unknownRgbSchema (toString pfa.schemaId))

/-! ## Safe height -/

-- the safe height is `tip - minConfirmations + 1`, never below 1
#guard safeHeightFor 5 0 == 6 && safeHeightFor 5 3 == 3 && safeHeightFor 5 5 == 1
#guard safeHeightFor 5 9 == 1 && safeHeightFor 0 0 == 1

/-- The witness mined at height 3, then two more blocks: tip 5, three confirmations. -/
def minedChain : Chain := (((chain0.broadcast niaW.tx).toOption.getD chain0).mine).mineN 2

def validateMined (minConf : Option Nat) :=
  validateConsignment "nia.rgb" niaFile (chainIndexer minedChain .bitcoinRegtest) noNet noWeb []
    minConf opts

-- the indexer gives the witness its height and time
#guard (validateMined none).map (·.witnesses)
  == .ok [⟨niaTxid, .mined 3 1700001200, false⟩]
-- mined at exactly the safe height is safe
#guard (validateMined (some 3)).map (fun v => (v.safeHeight, v.warnings)) == .ok (some 3, [])
-- one confirmation short: unsafe history
#guard (validateMined (some 4)).map (fun v => (v.safeHeight, v.warnings))
  == .ok (some 2, [.unsafeHistory [niaTxid]])
-- with a safe height, a tentative witness is unsafe even with no confirmation required
#guard (validateConsignmentWithResolver "nia.rgb" niaFile (chain0.resolver .bitcoinRegtest) none
    none (some (safeHeightFor 2 0)) offchain).map (·.warnings) == .ok [.unsafeHistory [niaTxid]]
-- the indexer must serve the requested network
#guard validateConsignment "nia.rgb" niaFile (chainIndexer minedChain .bitcoinMainnet) noNet
    noWeb [] none opts == .error (.invalidIndexer (reprStr WitnessResolverError.wrongChainNet))

/-! ## Mint lock status -/

-- the boundaries of rgb-lib's tests, with the finalized block at 0x20
#guard mintLockStatusOf (some 0x11) 0x12 0x20 == .confirmed
#guard mintLockStatusOf (some 0x11) 0x11 0x20 == .expired
#guard mintLockStatusOf none 0x22 0x20 == .pending
#guard mintLockStatusOf none 0x21 0x20 == .expired
#guard mintLockStatusOf none 0x10 0x20 == .expired

/-! ## A BFA mint -/

def bridgeAddress : EvmAddress := ⟨List.replicate 20 0xB1⟩
def listAddress : EvmAddress := ⟨List.replicate 20 0xC2⟩
def bridge : EvmContract := ⟨1, bridgeAddress⟩

/-- A BFA genesis granting one mint right on `utxoA`, with an optional reject list. -/
def bfaGenesis (rejectList : Option RejectListLocation) : Genesis :=
  { schemaId := bfa.schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList (
      [ (gsTicker, [⟨.unicodeTicker ⟨"BRG"⟩⟩]), (gsName, [⟨.name ⟨"Bridged"⟩⟩])
      , (gsPrecision, [⟨.precision .indivisible⟩]), (gsTerms, [⟨.contractTerms terms⟩])
      , (gsBridgeLocation, [⟨.bridgeLocation (.evm bridge)⟩]) ] ++
      (rejectList.map fun l => (gsRejectList, [⟨.rejectListLocation l⟩])).toList)
    assignments := OrdMap.ofList [(osMint, .declarative [.revealed ⟨utxoA.txid, utxoA.vout, 3⟩])] }

/-- Mint 500 units spending the mint right; the lock has to be included before block 30. -/
def mintOf (g : Genesis) : Transition :=
  { contractId := g.contractId, transitionType := tsMint, inputs := [⟨g.id, osMint, 0⟩]
    metadata := OrdMap.ofList [(msBeforeBlock, ⟨.blockNumber ⟨30⟩⟩)]
    globals := OrdMap.ofList [(gsIssuedSupply, [⟨.amount 500⟩])]
    assignments := OrdMap.ofList
      [(osAsset, .fungible [(.revealed (GraphSeal.witnessVout 1 9), ⟨500⟩)])] }

/-- The mint of genesis `g`: the transition, its witness bundle, the transfer file, the
claim it pushes, its lock id and the options taking the witness from the consignment. -/
structure Minted where
  mint : Transition
  witness : WitnessBundle
  file : ConsignmentFile
  claim : Claim
  lockId : LockId
  options : ValidationOptions

def mintedOf (g : Genesis) : Minted :=
  let t := mintOf g
  let w := witnessOf g.contractId [utxoA] [t]
  { mint := t, witness := w, file := .transfer { transfer := true, genesis := g, bundles := [w] }
    claim := .lock t.id w.witnessId 500 30, lockId := LockId.of t.id w.witnessId
    options := { opts with offchainTxid := some (toString w.witnessId) } }

def m : Minted := mintedOf (bfaGenesis none)
def mintId : String := toString m.mint.id

/-- An EVM chain 1 with the bridge, finalized at `fin` and five blocks past it. -/
def ledger (fin : Nat) (locks : List LockRecord) (lists : List EvmAccount := []) : EvmLedger :=
  { chainId := 1, latest := fin + 5, finalized := fin
    accounts := { address := bridgeAddress, code := .bridge locks 500 } :: lists }

def rpcUrl : String := "https://evm.example"
def urls : EvmRpcUrls := [(1, rpcUrl)]
def net (l : EvmLedger) : EvmNet := fun u => if u == rpcUrl then l.node else .unreachable
def lockAt (b : Nat) : LockRecord := ⟨m.lockId, 500, b⟩

-- the bridge records the inclusion block plus one, as of the queried block
#guard (ledger 20 [lockAt 10]).node.fundsInBlock bridgeAddress m.lockId 500 (.number 20)
  == .ok (some 10)
#guard (ledger 20 [lockAt 22]).node.fundsInBlock bridgeAddress m.lockId 500 (.number 20)
  == .ok none
-- the record is keyed by the amount too
#guard (ledger 20 [lockAt 10]).node.fundsInBlock bridgeAddress m.lockId 400 (.number 20)
  == .ok none
-- a lock recorded after the finalized block counts for `mint_lock_recorded` only
#guard (ledger 20 [lockAt 22]).node.mintLockRecorded bridgeAddress m.lockId 500 30 == .ok true
#guard (ledger 20 [lockAt 22]).node.circulatingSupply bridgeAddress == .ok (some 500)
-- an address without code records nothing
#guard (ledger 20 [lockAt 10]).node.fundsInBlock listAddress m.lockId 500 (.number 20)
  == .ok none

/-- Validate the mint with `validate_consignment`: claims go through the node of chain 1. -/
def validateMint (n : EvmNet) (u : EvmRpcUrls := urls) (x : Minted := m) (w : Web := noWeb) :=
  validateConsignment "mint.rgb" x.file (chainIndexer chain0 .bitcoinRegtest) n w u none
    x.options

-- lock included at block 10 and finalized: the mint is valid
#guard (validateMint (net (ledger 20 [lockAt 10]))).map (·.assetSchema) == .ok .bfa
-- no lock yet, and block 21 can still include it: not found
#guard validateMint (net (ledger 20 [])) == .error (.mintLockNotFound mintId)
-- a lock past the finalized block is not confirmed yet
#guard validateMint (net (ledger 20 [lockAt 22])) == .error (.mintLockNotFound mintId)
-- block 29 is finalized without the lock: it can never be confirmed
#guard validateMint (net (ledger 29 [])) == .error (.mintLockExpired mintId 30)
-- a lock included at block 30 is too late
#guard validateMint (net (ledger 35 [lockAt 30])) == .error (.mintLockExpired mintId 30)
-- no URL for the bridge's chain, a node on another chain, an unreachable node
#guard validateMint (net (ledger 20 [lockAt 10])) [] == .error (.noEvmRpcUrl 1)
#guard validateMint (net { ledger 20 [lockAt 10] with chainId := 137 })
  == .error (.evmChainIdMismatch 1 137)
#guard validateMint noNet == .error (.network "EVM RPC: error sending request")

/-- Validate the mint with `validate_consignment_with_resolver`. -/
def validateMintWith (r : Option ClaimResolver) :=
  validateConsignmentWithResolver "mint.rgb" m.file (chain0.resolver .bitcoinRegtest) r none
    none m.options

#guard validateMintWith (some (.custom 1 (· == m.claim))) matches .ok _
-- a custom resolver tells no expired mint from a pending one
#guard validateMintWith (some (.custom 1 fun _ => false)) == .error (.mintLockNotFound mintId)
#guard validateMintWith none == .error .noClaimResolver
#guard validateMintWith (some (.custom 137 fun _ => true)) == .error (.evmChainIdMismatch 1 137)
-- the checked resolver refuses a node on another chain
#guard (CheckedClaimResolver.check (.custom 137 fun _ => true) (.evm bridge)).map (fun _ => ())
  == .error (.wrongChainId 1 137)

/-! ## Reject lists -/

def listUrl : String := "https://issuer.example/list"
def listedGenesis : Genesis := bfaGenesis (some (.url ⟨listUrl⟩))
def urlListed : Minted := mintedOf listedGenesis
def minted : Opout := ⟨urlListed.mint.id, osAsset, 0⟩
def mintRightSpent : Opout := ⟨listedGenesis.id, osMint, 0⟩

/-- A resolver serving `body` at every URL. -/
def bodyList (body : String) : RejectListResolver where
  getUrlRejectList _ := .ok body
  getEvmRejectList _ := .error (.network "no EVM list")

def validateListed (rl : Option RejectListResolver) :=
  validateConsignmentWithResolver "mint.rgb" urlListed.file (chain0.resolver .bitcoinRegtest)
    (some (.custom 1 (· == urlListed.claim))) rl none urlListed.options

-- the terminal operation's inputs and outputs are the origins checked
#guard rejectCheckOrigins (match urlListed.file with | .transfer c => c | _ => default)
  == [mintRightSpent, minted]
-- a rejected terminal output refuses the consignment
#guard validateListed (some (bodyList (toString minted)))
  == .error (.consignmentRejected [toString minted])
-- the latest line wins: reject then allow accepts it
#guard validateListed (some (bodyList s!"{minted}\n!{minted}")) matches .ok _
-- a rejected input taints the output built on it
#guard validateListed (some (bodyList (toString mintRightSpent)))
  == .error (.consignmentRejected (sortStrings [toString mintRightSpent, toString minted]))
-- unknown lines are ignored
#guard validateListed (some (bodyList "# comment\n\n")) matches .ok _
-- an asset with a reject list needs a resolver
#guard validateListed none == .error .noRejectListResolver
-- the list is fetched even for a contract consignment, which has nothing to check
#guard validateConsignmentWithResolver "c.rgb"
    (.contract { transfer := false, genesis := listedGenesis })
    (chain0.resolver .bitcoinRegtest) none none none opts
  == .error .noRejectListResolver

/-- The issuer's server: the list at `listUrl`, a redirect elsewhere. -/
def web (body : String) : Web := fun u =>
  if u == listUrl then .ok (200, body)
  else if u == "https://issuer.example/moved" then .ok (302, "")
  else .error "error sending request"

-- `validate_consignment` reads a URL list over HTTP
#guard validateMint (net (ledger 20 [⟨urlListed.lockId, 500, 10⟩])) urls urlListed
    (web (toString minted))
  == .error (.consignmentRejected [toString minted])
#guard fetchUrlRejectList (web "x") listUrl == .ok "x"
#guard fetchUrlRejectList (web "x") "ftp://issuer.example/list"
  == .error (.rejectListService "unsupported reject list URL scheme: ftp")
-- a redirect is not followed: it is a failed request
#guard fetchUrlRejectList (web "x") "https://issuer.example/moved"
  == .error (.rejectListService "reject list request failed: HTTP 302")
#guard fetchUrlRejectList (web "x") "issuer.example"
  == .error (.rejectListService "relative URL without a base")
#guard fetchUrlRejectList (web "é") listUrl
  == .error (.rejectListService "reject list is not ASCII")

/-- A BFA asset whose reject list is kept by a contract on chain 1. -/
def evmListed : Minted := mintedOf (bfaGenesis (some (.evm ⟨1, listAddress⟩)))
def evmMinted : Opout := ⟨evmListed.mint.id, osAsset, 0⟩

/-- Chain 1 finalized at 20, latest 25: the bridge holds the lock, the list `entries`. -/
def listLedger (entries : List RejectListRecord) : EvmLedger :=
  ledger 20 [⟨evmListed.lockId, 500, 10⟩]
    [{ address := listAddress, deployedAt := 5, code := .rejectList entries }]

def validateEvmListed (entries : List RejectListRecord) :=
  validateMint (net (listLedger entries)) urls evmListed

#guard (validateEvmListed []) matches .ok _
-- a pending reject counts at once
#guard validateEvmListed [⟨evmMinted, true, 21⟩]
  == .error (.consignmentRejected [toString evmMinted])
-- a pending allow does not lift a finalized reject
#guard validateEvmListed [⟨evmMinted, true, 10⟩, ⟨evmMinted, false, 22⟩]
  == .error (.consignmentRejected [toString evmMinted])
-- a finalized allow does
#guard (validateEvmListed [⟨evmMinted, true, 10⟩, ⟨evmMinted, false, 12⟩]) matches .ok _
-- a list kept on a chain with no RPC URL cannot be read
def otherChainListed : Minted := mintedOf (bfaGenesis (some (.evm ⟨137, listAddress⟩)))
#guard validateMint (net (ledger 20 [⟨otherChainListed.lockId, 500, 10⟩])) urls otherChainListed
  == .error (.noEvmRpcUrl 137)
-- the node reports how many leading entries are finalized; pages hold the rest
#guard ((listLedger [⟨evmMinted, true, 10⟩, ⟨evmMinted, false, 22⟩]).node.rejectListEntries
    listAddress).map (·.finalized) == .ok 1
-- pages of one entry read the same list as pages of a thousand
def threeEntries : EvmNode :=
  (listLedger [⟨evmMinted, true, 10⟩, ⟨evmMinted, false, 12⟩, ⟨minted, true, 21⟩]).node
#guard threeEntries.rejectListEntriesPaged listAddress 1
  == threeEntries.rejectListEntries listAddress
#guard (threeEntries.rejectListEntries listAddress).map (fun l => (l.entries.length, l.finalized))
  == .ok (3, 2)
-- a list contract deployed after the finalized block has no finalized entry
def lateList : EvmAccount :=
  { address := listAddress, deployedAt := 22, code := .rejectList [⟨minted, true, 23⟩] }
#guard ((ledger 20 [] [lateList]).node.rejectListEntries listAddress).map
    (fun l => (l.entries.length, l.finalized)) == .ok (1, 0)
-- a list longer than the bound is refused before any page is read
def cheap : Opout := ⟨⟨Digest.of "op" []⟩, osAsset, 0⟩
#guard ((listLedger (List.replicate 100001 ⟨cheap, true, 6⟩)).node.rejectListEntries
    listAddress).map (·.finalized)
  == .error (.network "reject list too long: 100001 entries, at most 100000 supported")
-- no contract at the list address at the latest block
#guard (ledger 20 []).node.rejectListEntries listAddress
  == .error (.network s!"no contract at the reject list address {addressText listAddress}")

/-! ## ABI decoding -/

def opA : OpId := ⟨Digest.of "op" ["a"]⟩

#guard decodeRejectListEntries (encodeRejectListEntries [(⟨opA, osAsset, 2⟩, true)])
  == .ok [⟨toString (Opout.mk opA osAsset 2), true⟩]
#guard decodeRejectListEntries [.num 32, .num 1, .opid opA, .num 4000, .num 0, .num 2]
  == .error (abiError "bad bool")
#guard decodeRejectListEntries [.num 32, .num 1, .opid opA, .num 70000, .num 0, .num 1]
  == .error (abiError "bad uint16")
#guard decodeRejectListEntries [.num 33, .num 0] == .error (abiError "bad array offset")
#guard decodeRejectListEntries [.num 32, .num 2, .opid opA, .num 4000, .num 0, .num 1]
  == .error (abiError "bad array length")
#guard decodeRejectListEntries [] == .error (tooShort 0)

/-! ## Going online and received mints -/

def evmChain (min max : Nat) : List (Nat × EvmChain) := [(1, ⟨rpcUrl, min, max⟩)]

#guard checkEvmChains (net (ledger 20 [])) true (evmChain 5 10) == .ok (evmChain 5 10)
#guard checkEvmChains (net (ledger 20 [])) true (evmChain 11 10) == .error (.invalidEvmChain
  "chain ID 1: min_mint_lock_blocks (11) is greater than max_mint_lock_blocks (10)")
-- a wallet without BFA ignores its EVM chains
#guard checkEvmChains (net (ledger 20 [])) false (evmChain 11 10) == .ok []
#guard checkEvmChains (net { ledger 20 [] with chainId := 137 }) true (evmChain 5 10)
  == .error (.evmChainIdMismatch 1 137)
#guard checkEvmChains noNet true (evmChain 5 10)
  == .error (.invalidEvmRpcUrl "Network error: EVM RPC: error sending request")
-- a node that pruned the finalized state cannot confirm mints
#guard checkEvmChains (net { ledger 20 [] with stateFrom := 21 }) true (evmChain 5 10)
  == .error (.invalidEvmRpcUrl ("cannot read the state as of the latest finalized block, an " ++
    "endpoint keeping it is needed: Network error: eth_call error -32000: missing trie node"))

def saved : PendingMintLocks :=
  { consignmentDigest := "d1", evmChainId := 1, bridgeContract := bridgeAddress
    claims := [m.claim] }

-- a received mint waits while its lock is pending, and only then
#guard waitingForMintLocks (net (ledger 20 [])) urls (some saved) "d1" == .ok true
#guard waitingForMintLocks (net (ledger 20 [lockAt 10])) urls (some saved) "d1" == .ok false
#guard waitingForMintLocks (net (ledger 29 [])) urls (some saved) "d1" == .ok false
#guard waitingForMintLocks (net (ledger 20 [])) urls (some saved) "d2" == .ok false
#guard waitingForMintLocks (net { ledger 20 [] with chainId := 137 }) urls (some saved) "d1"
  == .ok false
-- a mint not recorded yet may commit to at most `max_mint_lock_blocks` after the latest block
#guard receivedMintTooFar false 31 20 10 && !receivedMintTooFar false 30 20 10
#guard !receivedMintTooFar true 31 20 10
-- temporary failures are sent again at most twice
#guard attemptsMade [.answered 503, .notSent false, .answered 502, .answered 200]
  == [.answered 503, .notSent false, .answered 502]
#guard attemptsMade [.notSent true, .answered 200] == [.notSent true]

/-! ## Inspection -/

def niaInspection := inspectConsignment "nia.rgb" niaFile .all

#guard niaInspection.map (fun i => (i.genesis.name, i.genesis.ticker, i.genesis.precision,
    i.genesis.issuedSupply)) == .ok ("Tether USD", some "USDT", 8, some 1000)
-- the input resolves from genesis to the input of the witness that spends it
#guard niaInspection.map (fun i => i.witnesses.map fun w => w.operations.map fun o =>
    o.transitions.map (·.inputs))
  == .ok [[[[⟨⟨toString niaGenesis.id, .asset, 0⟩, some 0, some (.fungible 1000)⟩]]]]
-- outputs: the concealed one shows the recipient id, the witness-output one the witness TXID
#guard niaInspection.map (fun i => i.witnesses.map fun w => w.operations.map fun o =>
    o.transitions.map (·.outputs))
  == .ok [[[[⟨none, none, none, .fungible 600, true, some s!"bcrt:{bobSeal.conceal}", none,
      some true⟩, ⟨some niaTxid, some 1, some 7, .fungible 400, false, none, none, some true⟩]]]]
#guard (inspectConsignment "nia.rgb" niaFile (.witness "zz")) == .error .invalidTxid
#guard (inspectConsignment "nia.rgb" niaFile (.witness (toString utxoA.txid)))
  == .error (.rgbInspection s!"witness {utxoA.txid} not found in the consignment")
-- validated consignment files are inspected too
#guard (inspectConsignment "nia.rgb" (.validated true niaConsignment) .terminals) matches .ok _

-- a BFA mint shows its bridge, its metadata and its issued supply
#guard (inspectConsignment "mint.rgb" m.file .terminals).map (fun i =>
    (i.genesis.bridgeLocation, i.genesis.issuedSupply, i.witnesses.map fun w =>
      w.operations.map fun o => o.transitions.map fun t => (t.type, t.globals, t.metadata)))
  == .ok (some (.evm ⟨1, addressText bridgeAddress⟩), none,
      [[[(.mint, [.issuedSupply 500], [.beforeBlock 30])]]])

/-- The fascia of the NIA transfer and its PSBT transaction. -/
def niaFascia : Fascia :=
  (commitBundles (mkTx [utxoA] [⟨0, .opReturn none⟩, ⟨546, .p2wpkh "issuer"⟩,
    ⟨9000, .p2wpkh "change"⟩]) [(niaCid, TransitionBundle.ofTransitions [niaTransfer])] 5
  ).toOption.getD default
def psbtTx : Tx := niaFascia.sealWitness.tx

def inspectNiaFascia (entropy : Option UInt64) (maxBundles : Nat := 4)
    (file : FasciaFile := .file 2000 (some niaFascia) false) :=
  inspectFascia psbtTx "op.fascia" file entropy 4096 maxBundles .regtest

-- without a wallet an input outside the bundle shows its opout only
#guard (inspectNiaFascia none).map (fun i => i.operations.map fun o => o.transitions.map (·.inputs))
  == .ok [[[⟨⟨toString niaGenesis.id, .asset, 0⟩, none, none⟩]]]
#guard (inspectNiaFascia (some 5)).map (·.txid) == .ok niaTxid
#guard inspectNiaFascia (some 6) == .error (.rgbInspection
  "the MPC commitment of the fascia was built with entropy 5, not the given 6")
#guard inspectNiaFascia none 0
  == .error (.rgbInspection "fascia bundle count 1 exceeds the maximum of 0")
#guard inspectNiaFascia none 4 (.file 5000 (some niaFascia) false)
  == .error (.fileTooLarge "op.fascia" 4096)
#guard inspectNiaFascia none 4 (.file 2000 (some niaFascia) true)
  == .error (.invalidFilePath "op.fascia")
#guard inspectFascia (mkTx [utxoB] []) "op.fascia" (.file 2000 (some niaFascia) false) none 4096
    4 .regtest
  == .error (.rgbInspection
    s!"fascia witness ID {niaW.witnessId} does not match PSBT TXID {(mkTx [utxoB] []).txid}")

/-! ## SPV proofs -/

def filled := fillSpvProofs "nia.rgb" niaFile (chainIndexer minedChain .bitcoinRegtest)

-- the mined witness gets its proof and the file is rewritten
#guard filled.map (·.1) == .ok ⟨[], true⟩
#guard filled.map (fun r => r.2.map fun c => c.bundles.map (·.spvProof.isSome)) == .ok (some [true])
/-- The consignment `fill_spv_proofs` rewrote. -/
def refilled : Consignment := match filled with
  | .ok (_, some c) => c
  | _ => niaConsignment

/-- A resolver that serves block headers and finds no witness. -/
def headersOnly : Resolver :=
  { minedChain.resolver .bitcoinRegtest with resolveWitness := fun _ => .ok .unresolved }

-- validation then reads the position from the proof and the header alone
#guard (validateConsignmentWithResolver "nia.rgb" (.transfer refilled) headersOnly none none none
    opts).map (·.witnesses) == .ok [⟨niaTxid, .mined 3 1700001200, false⟩]
#guard validateConsignmentWithResolver "nia.rgb" niaFile headersOnly none none none opts
  matches .error (.consignmentValidationFailed _)
-- a witness not mined yet is reported, and the file is left as it is
#guard fillSpvProofs "nia.rgb" niaFile (chainIndexer chain0 .bitcoinRegtest)
  == .ok (⟨[⟨niaTxid, "transaction not mined"⟩], false⟩, none)
-- only a transfer consignment, with an indexer of its network
#guard fillSpvProofs "nia.rgb" (.contract niaConsignment) (chainIndexer chain0 .bitcoinRegtest)
  == .error .invalidConsignment
#guard fillSpvProofs "nia.rgb" niaFile (chainIndexer chain0 .bitcoinMainnet)
  == .error (.invalidIndexer (reprStr WitnessResolverError.wrongChainNet))

end Rgb.Examples.NoWalletScenario
