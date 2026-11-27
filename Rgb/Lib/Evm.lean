import Rgb.Lib.Error
import Rgb.Lib.RejectList
import Rgb.Consensus.Validation

/-!
# EVM reads

rgb-lib reads an EVM chain through a JSON-RPC node and never sends transactions to it.
It reads:

* from the bridge contract of a BFA asset, the lock that confirms a mint
  (`getFundsInBlock(lockId, amount)`: the inclusion block plus one, or zero) as of the
  latest finalized block, and the circulating supply (`circulatingSupply()`);
* from an `IRgbRejectList` contract, a reject list (`length()`, then `entries(start, end)`
  in pages);
* the chain id, the latest block and the latest finalized block.

`EvmNode` is what a node answers; `EvmLedger` is a symbolic chain whose node answers
honestly. Call results are ABI words: a number or an operation id.

| failure | `Rgb.Lib.Error` |
|---|---|
| a request fails, the node reports an error, an answer does not decode | `network` |
| no RPC URL is configured for the chain | `noEvmRpcUrl` |
| the node is on another chain | `evmChainIdMismatch` |
| going online: chain id, finalized block or its state unreadable | `invalidEvmRpcUrl` |
| going online: `min_mint_lock_blocks` above `max_mint_lock_blocks` | `invalidEvmChain` |
| a mint lock can no longer be included in time | `mintLockExpired` |
| a mint lock is not confirmed | `mintLockNotFound` |
-/

namespace Rgb.Lib.Evm

/-! ## Constants -/

/-- Selector of `getFundsInBlock(uint256,uint256)` (bridge contract). -/
def fundsInBlockSelector : String := "0x2ce06e2d"
/-- Selector of `circulatingSupply()` (bridge contract). -/
def circulatingSupplySelector : String := "0x9358928b"
/-- Selector of `length()` (reject list contract). -/
def rejectListLengthSelector : String := "0x1f7b6d32"
/-- Selector of `entries(uint256,uint256)` (reject list contract). -/
def rejectListEntriesSelector : String := "0x17b937e6"
/-- Most entries one `entries` call asks for (`REJECT_LIST_PAGE_SIZE`). -/
def rejectListPageSize : Nat := 1000
/-- Times a request is sent again after a temporary failure (`RPC_RETRIES`). -/
def rpcRetries : Nat := 2
/-- Pause before retry `n`, in seconds (`RPC_RETRY_PAUSE` times `n`). -/
def rpcRetryPause (n : Nat) : Nat := n

/-- Saturating `u64` addition, as rgb-lib adds block numbers. -/
def satAdd (a b : Nat) : Nat := min (a + b) Bound.u64

/-! ## Text forms -/

/-- An address as `0x` and its hex bytes (`EvmAddress` display). -/
def addressText (a : EvmAddress) : String := "0x" ++ Hex.ofBytes a.bytes

/-- The address `check_mint_support` calls (`EvmAddress::default`, twenty zero bytes). -/
def zeroAddress : EvmAddress := ⟨List.replicate 20 0⟩

/-- How rgb-lib displays an error that ends up in the details of another one. -/
def errorText : Error → String
  | .network d => s!"Network error: {d}"
  | e => reprStr e

/-! ## Sending a request -/

/-- One attempt to send a request: the HTTP status of the answer, or a send failure. -/
inductive Attempt where
  | answered (status : Nat)
  /-- Not sent: timed out, or failed otherwise (a refused connection, a failed lookup). -/
  | notSent (timeout : Bool)
  deriving DecidableEq, Repr

/-- A temporary failure: HTTP 502, 503 or 504, or a send failure other than a timeout. -/
def Attempt.temporary : Attempt → Bool
  | .answered s => s == 502 || s == 503 || s == 504
  | .notSent timeout => !timeout

/-- The attempts `post` makes when they go as `outcomes` (`EvmClient::post`). -/
def attemptsMade (outcomes : List Attempt) : List Attempt :=
  let rec go : Nat → List Attempt → List Attempt
    | _, [] => []
    | retries, a :: rest =>
      if !a.temporary || retries == rpcRetries then [a] else a :: go (retries + 1) rest
  go 0 outcomes

/-! ## ABI words and calls -/

/-- A 32-byte ABI word: a number below 2^256, or an operation id (a hash). -/
inductive AbiWord where
  | num (n : Nat)
  | opid (o : OpId)
  deriving DecidableEq, Repr, Inhabited

/-- A network error for an answer that does not decode (`abi_error`). -/
def abiError (details : String) : Error := .network s!"invalid ABI data: {details}"

/-- The error for data shorter than word `i`. -/
def tooShort (i : Nat) : Error :=
  .network s!"ABI data too short: expected at least {64 * (i + 1)} hex chars"

/-- Word `i` as a `u64`, none when it does not fit (`abi_word_u64`); the model takes an
operation id to have a non-zero high part. -/
def wordU64 (ws : List AbiWord) (i : Nat) : Except Error (Option Nat) :=
  match ws[i]? with
  | none => .error (tooShort i)
  | some (.num n) => .ok (if n < 2 ^ 64 then some n else none)
  | some (.opid _) => .ok none

/-- Word `i` as a `uint16` (`abi_word_u16`). -/
def wordU16 (ws : List AbiWord) (i : Nat) : Except Error Nat := do
  match ← wordU64 ws i with
  | some v => if v ≤ 0xFFFF then pure v else throw (abiError "bad uint16")
  | none => throw (abiError "bad uint16")

/-- Word `i` as an operation id; a number reads as an id no operation of the model has. -/
def wordOpId (ws : List AbiWord) (i : Nat) : Except Error OpId :=
  match ws[i]? with
  | none => .error (tooShort i)
  | some (.opid o) => .ok o
  | some (.num n) => .ok ⟨Digest.of "evm:bytes32" [encode n]⟩

/-- Decode an `entries` page, an ABI `(bytes32,uint16,uint16,bool)[]`
(`decode_reject_list_entries`); data after the array is ignored. -/
def decodeRejectListEntries (ws : List AbiWord) : Except Error (List EvmRejectListEntry) := do
  let words := ws.length
  let lenIndex ← match ← wordU64 ws 0 with
    | some o =>
      if o % 32 == 0 && o / 32 < words then pure (o / 32) else throw (abiError "bad array offset")
    | none => throw (abiError "bad array offset")
  let len ← match ← wordU64 ws lenIndex with
    | some l =>
      if lenIndex + 1 + 4 * l ≤ words then pure l else throw (abiError "bad array length")
    | none => throw (abiError "bad array length")
  (List.range len).mapM fun i => do
    let base := lenIndex + 1 + 4 * i
    let op ← wordOpId ws base
    let ty ← wordU16 ws (base + 1)
    let no ← wordU16 ws (base + 2)
    let reject ← match ← wordU64 ws (base + 3) with
      | some 0 => pure false
      | some 1 => pure true
      | _ => throw (abiError "bad bool")
    let o : Opout := ⟨op, ⟨ty.toUInt16⟩, no.toUInt16⟩
    pure ⟨toString o, reject⟩

/-- ABI words of an `entries` page: offset, length, then four words per entry. -/
def encodeRejectListEntries (es : List (Opout × Bool)) : List AbiWord :=
  [.num 32, .num es.length] ++ es.flatMap fun (o, r) =>
    [.opid o.op, .num o.ty.v.toNat, .num o.no.toNat, .num (if r then 1 else 0)]

/-- The contract calls rgb-lib makes (`eth_call` data). -/
inductive EvmCall where
  /-- `getFundsInBlock(lockId, amount)` -/
  | fundsInBlock (lockId : LockId) (amount : UInt64)
  /-- `circulatingSupply()` -/
  | circulatingSupply
  /-- `length()` -/
  | rejectListLength
  /-- `entries(start, end)` -/
  | rejectListEntries (start stop : Nat)
  /-- Empty call data (`0x`). -/
  | empty
  deriving DecidableEq, Repr

/-- Selector the call data starts with (`0x` alone for empty data). -/
def EvmCall.selector : EvmCall → String
  | .fundsInBlock .. => fundsInBlockSelector
  | .circulatingSupply => circulatingSupplySelector
  | .rejectListLength => rejectListLengthSelector
  | .rejectListEntries .. => rejectListEntriesSelector
  | .empty => "0x"

/-- The block an `eth_call` reads the state as of (`CallBlock`). -/
inductive CallBlock where
  | number (n : Nat)
  | latest
  deriving DecidableEq, Repr

/-- The JSON-RPC block parameter: a hex number or the `latest` tag. -/
def CallBlock.param : CallBlock → String
  | .number n => "0x" ++ String.ofList (Nat.toDigits 16 n)
  | .latest => "latest"

/-- What a node answers to an `eth_call`. -/
inductive CallAnswer where
  /-- The request failed (send, HTTP or JSON decoding): the network error details. -/
  | failed (details : String)
  /-- A JSON-RPC error; a revert has a message starting with `execution reverted`. -/
  | rpcError (code : Int) (message : String)
  /-- A null result. -/
  | null
  /-- Returned data as ABI words; `[]` is `0x`, the answer of an address with no code. -/
  | data (words : List AbiWord)
  deriving DecidableEq, Repr

/-- The answer of a call that reverts. -/
def CallAnswer.reverted : CallAnswer := .rpcError 3 "execution reverted"

/-- The network error of a JSON-RPC error answer (`rpc_error`). -/
def rpcError (method : String) (code : Int) (message : String) : Error :=
  .network s!"{method} error {code}: {message}"

/-- The network error of a null result (`null_result`). -/
def nullResult (method : String) : Error := .network s!"{method} returned null result"

/-! ## Nodes -/

/-- An EVM JSON-RPC node: what it answers to each request rgb-lib sends; a request that
fails gives the network error rgb-lib reports for it. -/
structure EvmNode where
  /-- `eth_chainId` -/
  chainId : Except Error Nat
  /-- `eth_blockNumber` -/
  blockNumber : Except Error Nat
  /-- `eth_getBlockByNumber("finalized")`; none when the node reports no finalized block. -/
  finalizedBlock : Except Error (Option Nat)
  /-- `eth_call` of a contract as of a block. -/
  call : EvmAddress → EvmCall → CallBlock → CallAnswer

/-- A node nothing answers at: every request fails to be sent. -/
def EvmNode.unreachable : EvmNode where
  chainId := .error (.network "EVM RPC: error sending request")
  blockNumber := .error (.network "EVM RPC: error sending request")
  finalizedBlock := .error (.network "EVM RPC: error sending request")
  call _ _ _ := .failed "EVM RPC: error sending request"

/-- A lock a bridge records, keyed by lock id and amount, with its inclusion block. -/
structure LockRecord where
  lockId : LockId
  amount : UInt64
  block : Nat
  deriving DecidableEq, Repr

/-- An entry of a reject list contract and the block it was appended in. -/
structure RejectListRecord where
  opout : Opout
  reject : Bool
  block : Nat
  deriving DecidableEq, Repr

/-- Code at an address. -/
inductive EvmCode where
  /-- A bridge (`MinimalBridge`): permanent lock records and the circulating supply. -/
  | bridge (locks : List LockRecord) (circulating : Nat)
  /-- An append-only reject list (`IRgbRejectList`). -/
  | rejectList (entries : List RejectListRecord)
  /-- Code without the functions rgb-lib calls: every call reverts. -/
  | other
  deriving DecidableEq, Repr

/-- A contract and the block it was deployed in. -/
structure EvmAccount where
  address : EvmAddress
  deployedAt : Nat := 0
  code : EvmCode
  deriving DecidableEq, Repr

/-- What a contract's code answers to a call as of block `n`. -/
def EvmCode.answer : EvmCode → EvmCall → Nat → CallAnswer
  | .bridge locks _, .fundsInBlock id amount, n =>
    match locks.find? fun r => r.lockId == id && r.amount == amount && r.block ≤ n with
    | some r => .data [.num (r.block + 1)]
    | none => .data [.num 0]
  | .bridge _ circulating, .circulatingSupply, _ => .data [.num circulating]
  | .rejectList es, .rejectListLength, n => .data [.num (es.filter (·.block ≤ n)).length]
  | .rejectList es, .rejectListEntries start stop, n =>
    let live := es.filter (·.block ≤ n)
    if start ≤ stop && stop ≤ live.length then
      .data (encodeRejectListEntries (((live.drop start).take (stop - start)).map
        fun r => (r.opout, r.reject)))
    else .reverted
  | _, _, _ => .reverted

/-- A symbolic EVM chain: its id, latest and finalized blocks, and its contracts. -/
structure EvmLedger where
  chainId : Nat
  latest : Nat
  finalized : Nat
  accounts : List EvmAccount := []
  /-- Oldest block whose state the node keeps; older state is pruned. -/
  stateFrom : Nat := 0
  deriving DecidableEq, Repr

namespace EvmLedger

/-- `eth_call` as of a block: a future block or pruned state is an RPC error, an address
without code (yet) returns no data. -/
def answer (l : EvmLedger) (a : EvmAddress) (c : EvmCall) (b : CallBlock) : CallAnswer :=
  let n := match b with
    | .number n => n
    | .latest => l.latest
  if n > l.latest then .rpcError (-32000) "header not found"
  else if n < l.stateFrom then .rpcError (-32000) "missing trie node"
  else match l.accounts.find? fun acc => acc.address == a && acc.deployedAt ≤ n with
    | none => .data []
    | some acc => acc.code.answer c n

/-- The honest node of the ledger. -/
def node (l : EvmLedger) : EvmNode where
  chainId := .ok l.chainId
  blockNumber := .ok l.latest
  finalizedBlock := .ok (some l.finalized)
  call := l.answer

end EvmLedger

/-! ## Client requests (`EvmClient`) -/

namespace EvmNode

/-- `eth_call`: an RPC error, a revert included, or a null result fails. -/
def ethCall (n : EvmNode) (a : EvmAddress) (c : EvmCall) (b : CallBlock) :
    Except Error (List AbiWord) :=
  match n.call a c b with
  | .failed d => .error (.network d)
  | .rpcError code msg => .error (rpcError "eth_call" code msg)
  | .null => .error (nullResult "eth_call")
  | .data ws => .ok ws

/-- `eth_call_unless_reverted`: a revert reads as none. -/
def ethCallUnlessReverted (n : EvmNode) (a : EvmAddress) (c : EvmCall) (b : CallBlock) :
    Except Error (Option (List AbiWord)) :=
  match n.call a c b with
  | .rpcError code msg =>
    if msg.startsWith "execution reverted" then .ok none else .error (rpcError "eth_call" code msg)
  | _ => (n.ethCall a c b).map some

/-- The latest finalized block (`finalized_block_number`). -/
def finalizedBlockNumber (n : EvmNode) : Except Error Nat :=
  match n.finalizedBlock with
  | .error e => .error e
  | .ok none => .error (.network "the node reports no finalized block")
  | .ok (some b) => .ok b

/-- The block a lock was included in, as the bridge records it as of `block`
(`funds_in_block`): no code, a revert and a zero record are none. -/
def fundsInBlock (n : EvmNode) (contract : EvmAddress) (lockId : LockId) (amount : UInt64)
    (block : CallBlock) : Except Error (Option Nat) := do
  match ← n.ethCallUnlessReverted contract (.fundsInBlock lockId amount) block with
  | none | some [] => pure none
  | some [w] =>
    match ← wordU64 [w] 0 with
    | none => throw (abiError "lock block doesn't fit in a u64")
    | some 0 => pure none
    | some k => pure (some (k - 1))
  | some _ => throw (abiError "unexpected getFundsInBlock result size")

/-- The circulating supply the bridge accounts as of the latest block
(`circulating_supply`); none when the contract does not account it. -/
def circulatingSupply (n : EvmNode) (contract : EvmAddress) : Except Error (Option Nat) := do
  match ← n.ethCallUnlessReverted contract .circulatingSupply .latest with
  | none | some [] => pure none
  | some [w] =>
    match ← wordU64 [w] 0 with
    | some v => pure (some v)
    | none => throw (abiError "circulating supply doesn't fit in a u64")
  | some _ => throw (abiError "unexpected circulatingSupply result size")

/-- Length of a reject list as of `block` (`reject_list_length`); none when there is no code
at the address. A revert is an error. -/
def rejectListLength (n : EvmNode) (contract : EvmAddress) (block : Nat) :
    Except Error (Option Nat) := do
  let ws ← n.ethCall contract .rejectListLength (.number block)
  if ws.isEmpty then return none
  match ← wordU64 ws 0 with
  | some l => pure (some l)
  | none => throw (abiError "reject list length doesn't fit in a u64")

/-- Pages `[start, min(start + pageSize, len))` read as of `block`, in order; each must hold
exactly the entries asked for. -/
def readPages (n : EvmNode) (contract : EvmAddress) (block pageSize len : Nat) :
    Nat → Nat → List EvmRejectListEntry → Except Error (List EvmRejectListEntry)
  | 0, _, acc => .ok acc
  | fuel + 1, start, acc =>
    if start < len then do
      let stop := min (start + pageSize) len
      let page ← decodeRejectListEntries
        (← n.ethCall contract (.rejectListEntries start stop) (.number block))
      if page.length != stop - start then throw (abiError "unexpected reject list page size")
      readPages n contract block pageSize len fuel stop (acc ++ page)
    else .ok acc

/-- All entries of a reject list contract and how many are finalized
(`reject_list_entries_paged`); no code at the finalized block means no finalized entry. -/
def rejectListEntriesPaged (n : EvmNode) (contract : EvmAddress) (pageSize : Nat) :
    Except Error EvmRejectList := do
  let block ← n.blockNumber
  let finalized := min (← n.finalizedBlockNumber) block
  let finalizedLen := (← n.rejectListLength contract finalized).getD 0
  let some len ← n.rejectListLength contract block
    | throw (.network s!"no contract at the reject list address {addressText contract}")
  if finalizedLen > len then
    throw (.network "reject list shorter at the latest block than at the finalized one")
  if len > maxRejectListEntries then
    throw (.network
      s!"reject list too long: {len} entries, at most {maxRejectListEntries} supported")
  let entries ← n.readPages contract block pageSize len (len + 1) 0 []
  return { entries, finalized := finalizedLen }

/-- All entries of a reject list contract, `rejectListPageSize` per page
(`reject_list_entries`). -/
def rejectListEntries (n : EvmNode) (contract : EvmAddress) : Except Error EvmRejectList :=
  n.rejectListEntriesPaged contract rejectListPageSize

/-- The node serves what confirming mints needs (`check_mint_support`): the latest finalized
block and the state as of it. -/
def checkMintSupport (n : EvmNode) : Except Error Unit := do
  let fin ← n.finalizedBlockNumber.mapError fun e =>
    .invalidEvmRpcUrl s!"cannot get the latest finalized block: {errorText e}"
  match n.ethCall zeroAddress .empty (.number fin) with
  | .ok _ => pure ()
  | .error e =>
    throw (.invalidEvmRpcUrl ("cannot read the state as of the latest finalized block, " ++
      s!"an endpoint keeping it is needed: {errorText e}"))

end EvmNode

/-! ## Mint locks -/

/-- Status of the lock confirming a mint (`MintLockStatus`). -/
inductive MintLockStatus where
  /-- Recorded, included before the block the mint commits to. -/
  | confirmed
  /-- Not recorded yet, and it may still be included in time. -/
  | pending
  /-- Never confirmed: no block it could be included in is left. -/
  | expired
  deriving DecidableEq, Repr

/-- The status of a lock from its record as of the finalized block (`mint_lock_status`): a
lock not recorded as of the finalized block can only be included after it. -/
def mintLockStatusOf (record : Option Nat) (beforeBlock finalized : Nat) : MintLockStatus :=
  match record with
  | some b => if b < beforeBlock then .confirmed else .expired
  | none => if satAdd finalized 1 ≥ beforeBlock then .expired else .pending

/-- The status of the lock of `amount` with id `lockId`, read as of `finalized`. -/
def EvmNode.mintLockStatus (n : EvmNode) (contract : EvmAddress) (lockId : LockId)
    (amount : UInt64) (beforeBlock finalized : Nat) : Except Error MintLockStatus := do
  let record ← n.fundsInBlock contract lockId amount (.number finalized)
  return mintLockStatusOf record beforeBlock finalized

/-- The bridge records the lock as of the latest block, finalized or not, included before
`beforeBlock` (`mint_lock_recorded`). -/
def EvmNode.mintLockRecorded (n : EvmNode) (contract : EvmAddress) (lockId : LockId)
    (amount : UInt64) (beforeBlock : Nat) : Except Error Bool := do
  match ← n.fundsInBlock contract lockId amount .latest with
  | some b => pure (b < beforeBlock)
  | none => pure false

/-! ## Endpoints -/

/-- EVM JSON-RPC URLs by the chain id they are configured for (`evm_rpc_urls`). -/
abbrev EvmRpcUrls := List (Nat × String)

/-- The node that answers at each URL. -/
abbrev EvmNet := String → EvmNode

/-- The client for a chain (`evm_client`): the node at its configured URL. -/
def evmClient (net : EvmNet) (urls : EvmRpcUrls) (chainId : Nat) : Except Error EvmNode :=
  match urls.lookup chainId with
  | none => .error (.noEvmRpcUrl chainId)
  | some url => .ok (net url)

/-- The client for a chain, checked to be connected to it (`checked_evm_client`). -/
def checkedEvmClient (net : EvmNet) (urls : EvmRpcUrls) (chainId : Nat) :
    Except Error EvmNode := do
  let n ← evmClient net urls chainId
  let actual ← n.chainId
  if actual != chainId then throw (.evmChainIdMismatch chainId actual)
  return n

/-- The entries of a reject list contract through the URL of its chain; the node's chain is
checked first unless the wallet checked it when going online. -/
def readEvmRejectList (net : EvmNet) (urls : EvmRpcUrls) (chainsChecked : Bool)
    (c : EvmContract) : Except Error EvmRejectList := do
  let n ← if chainsChecked then evmClient net urls c.chainId.toNat
    else checkedEvmClient net urls c.chainId.toNat
  n.rejectListEntries c.address

/-! ## Claim resolvers -/

/-- Why a claim cannot be confirmed (`ClaimResolverError`). -/
inductive ClaimResolverError where
  /-- The resolver is on another chain than the bridge. -/
  | wrongChainId (expected actual : Nat)
  /-- The bridge does not confirm the claim of this operation. -/
  | unconfirmed (opid : OpId)
  | resolverIssue (details : String)
  | validation (e : ValidationError)
  deriving DecidableEq, Repr

/-- The rgb-lib error of a claim resolver error. -/
def ClaimResolverError.toError : ClaimResolverError → Error
  | .wrongChainId expected actual => .evmChainIdMismatch expected actual
  | .unconfirmed opid => .mintLockNotFound (toString opid)
  | .resolverIssue d => .network d
  | .validation e => .internal s!"unexpected claim resolution error: {reprStr e}"

/-- A claim resolver (`ResolveClaim`): the chain id its node reports, and whether the bridge
at a location holds a claim's lock. `isConfirmed` takes and returns the opids of the mints
found expired so far (`MintClaimResolver.expired`). -/
structure ClaimResolver where
  evmChainId : Except ClaimResolverError Nat
  isConfirmed : List OpId → BridgeLocation → Claim → Except ClaimResolverError (Bool × List OpId)

/-- A resolver on chain `chainId` confirming the claims `confirmed` accepts; it finds no mint
expired. -/
def ClaimResolver.custom (chainId : Nat) (confirmed : Claim → Bool) : ClaimResolver where
  evmChainId := .ok chainId
  isConfirmed expired _ c := .ok (confirmed c, expired)

/-- A resolver checked to be on the chain of the bridge location (`CheckedClaimResolver`). -/
structure CheckedClaimResolver where
  inner : ClaimResolver
  location : BridgeLocation

/-- Check a resolver against a bridge location (`CheckedClaimResolver::with`). -/
def CheckedClaimResolver.check (inner : ClaimResolver) (location : BridgeLocation) :
    Except ClaimResolverError CheckedClaimResolver := do
  match location with
  | .evm c =>
    let actual ← inner.evmChainId
    if actual != c.chainId.toNat then throw (.wrongChainId c.chainId.toNat actual)
  return ⟨inner, location⟩

/-- Ask whether a claim is confirmed at the checked location. -/
def CheckedClaimResolver.isConfirmed (r : CheckedClaimResolver) (expired : List OpId)
    (c : Claim) : Except ClaimResolverError (Bool × List OpId) :=
  r.inner.isConfirmed expired r.location c

/-- A client failure as a resolver issue, network details as they are (`resolver_issue`). -/
def resolverIssue : Error → ClaimResolverError
  | .network d => .resolverIssue d
  | e => .resolverIssue (reprStr e)

/-- The claim resolver over a node (`MintClaimResolver`). The node's answers do not change, so
reading the finalized block once per validation or once per claim gives the same block. -/
def mintClaimResolver (n : EvmNode) : ClaimResolver where
  evmChainId := n.chainId.mapError resolverIssue
  isConfirmed expired loc c :=
    match loc with
    | .evm contract => do
      let fin ← n.finalizedBlockNumber.mapError resolverIssue
      let st ← n.mintLockStatus contract.address c.lockId c.amount c.beforeBlock.toNat fin
        |>.mapError resolverIssue
      pure (st == .confirmed, if st == .expired then expired ++ [c.opid] else expired)

/-! ## Going online -/

/-- An EVM chain of `OnlineOptions.evm_chains` (`EvmChain`): its RPC URL, and the bounds, in
blocks after the latest one, of the block a mint commits to. -/
structure EvmChain where
  rpcUrl : String
  minMintLockBlocks : Nat
  maxMintLockBlocks : Nat
  deriving DecidableEq, Repr

/-- `check_evm_chains`: a wallet without BFA ignores the chains. Chains are checked in list
order (in any order in rgb-lib). -/
def checkEvmChains (net : EvmNet) (supportsBfa : Bool) (chains : List (Nat × EvmChain)) :
    Except Error (List (Nat × EvmChain)) := do
  if !supportsBfa then return []
  for (chainId, c) in chains do
    if c.minMintLockBlocks > c.maxMintLockBlocks then
      throw (.invalidEvmChain (s!"chain ID {chainId}: min_mint_lock_blocks " ++
        s!"({c.minMintLockBlocks}) is greater than max_mint_lock_blocks ({c.maxMintLockBlocks})"))
    let n := net c.rpcUrl
    let actual ← n.chainId.mapError fun e => .invalidEvmRpcUrl (errorText e)
    if actual != chainId then throw (.evmChainIdMismatch chainId actual)
    n.checkMintSupport
  return chains

/-! ## Received mints -/

/-- Claims a received mint waits for (`PendingMintLocks`), saved with the digest of the
consignment they are for. -/
structure PendingMintLocks where
  consignmentDigest : String
  evmChainId : Nat
  bridgeContract : EvmAddress
  claims : List Claim
  deriving DecidableEq, Repr

/-- The received consignment with digest `digest` still waits for its saved mint locks
(`waiting_for_mint_locks`): none expired and some not confirmed. -/
def waitingForMintLocks (net : EvmNet) (urls : EvmRpcUrls) (saved : Option PendingMintLocks)
    (digest : String) : Except Error Bool := do
  let some p := saved | return false
  if p.consignmentDigest != digest then return false
  let some url := urls.lookup p.evmChainId | return false
  let location : BridgeLocation := .evm ⟨p.evmChainId.toUInt64, p.bridgeContract⟩
  match CheckedClaimResolver.check (mintClaimResolver (net url)) location with
  | .error (.wrongChainId ..) => return false
  | .error e => throw e.toError
  | .ok r =>
    let mut unconfirmed := 0
    let mut expired : List OpId := []
    for c in p.claims do
      let (ok, ex) ← (r.isConfirmed expired c).mapError ClaimResolverError.toError
      expired := ex
      if !ok then
        if expired.contains c.opid then return false
        unconfirmed := unconfirmed + 1
    return unconfirmed > 0

/-- A received mint whose lock is not recorded yet is refused when the block it commits to
is more than `maxMintLockBlocks` after the latest block. -/
def receivedMintTooFar (committed : Bool) (beforeBlock latest maxMintLockBlocks : Nat) : Bool :=
  !committed && beforeBlock > satAdd latest maxMintLockBlocks

/-- A mint its recipient checked (`ReceivedMint`, saved as `rcv_mint.json`): what its sender has
to lock on the bridge. -/
structure ReceivedMint where
  opid : String
  /-- The lock's id; rgb-lib saves its hex text. -/
  lockId : LockId
  amount : Nat
  beforeBlock : Nat
  evmChainId : Nat
  /-- The bridge contract's address as text. -/
  bridgeContract : String
  deriving DecidableEq, Repr, Inhabited

/-! ## Sent mints -/

/-- The bounds `mint_begin` puts on the block a lock is included before, the latest block of the
bridge's chain being `latest`: a block is left for the lock, and it is at least
`minMintLockBlocks` and at most `maxMintLockBlocks` after the latest block. -/
def checkMintBeforeBlock (beforeBlock latest : Nat) (c : EvmChain) : Except Error Unit := do
  if beforeBlock ≤ satAdd latest 1 then
    throw (.invalidBeforeBlock (s!"the lock cannot be included before block {beforeBlock}, " ++
      s!"the latest external chain block being {latest}"))
  if beforeBlock < satAdd latest c.minMintLockBlocks then
    throw (.invalidBeforeBlock (s!"block {beforeBlock} is less than {c.minMintLockBlocks} " ++
      s!"blocks after the latest external chain block {latest}"))
  if beforeBlock > satAdd latest c.maxMintLockBlocks then
    throw (.invalidBeforeBlock (s!"block {beforeBlock} is more than {c.maxMintLockBlocks} " ++
      s!"blocks after the latest external chain block {latest}"))

/-- A mint as its sender knows it (`SentMint`): what its lock on the bridge has to match. -/
structure SentMint where
  contractId : ContractId
  opid : OpId
  /-- Commits to the mint operation and to its witness transaction. -/
  lockId : LockId
  amount : UInt64
  beforeBlock : Nat
  bridgeLocation : BridgeLocation
  deriving DecidableEq, Repr

/-- `check_mint_lock`: the bridge records the mint's lock as of the latest finalized block,
included before the block the mint commits to. Gives the node of the bridge's chain. -/
def checkMintLock (net : EvmNet) (urls : EvmRpcUrls) (m : SentMint) : Except Error EvmNode := do
  match m.bridgeLocation with
  | .evm c =>
    let n ← evmClient net urls c.chainId.toNat
    let fin ← n.finalizedBlockNumber
    match ← n.mintLockStatus c.address m.lockId m.amount m.beforeBlock fin with
    | .confirmed => return n
    | .pending => throw (.mintLockNotFound (toString m.opid))
    | .expired => throw (.mintLockExpired (toString m.opid) m.beforeBlock)

/-- `read_bridge_circulating_supply`: the supply the bridge accounts, when it can be read. -/
def readCirculatingSupply (n : EvmNode) (contract : EvmAddress) : Option Nat :=
  match n.circulatingSupply contract with
  | .ok s => s
  | .error _ => none

end Rgb.Lib.Evm
