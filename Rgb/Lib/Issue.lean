import Rgb.Lib.Vanilla

/-!
# Issuance

`issue_asset_nia`, `_cfa`, `_uda`, `_ifa` and `_bfa` create a contract whose
genesis assigns state to the wallet's own UTXOs. Issuance is offline. Inputs are
checked in rgb-lib's order; every allocation goes to a different UTXO (asset
state to a UTXO with a free slot, inflation/link/mint rights to an empty one).
The contract is validated, imported into the stash, and recorded as a settled
incoming transfer of kind `issuance`.
-/

namespace Rgb.Lib

/-! ## Input checks -/

/-- `check_ticker`: all uppercase, then a `Ticker` (a letter, then letters or digits, 1 to 8). -/
def checkTicker (t : String) : Result Unit :=
  if t.toUpper != t then .error (.invalidTicker "ticker needs to be all uppercase")
  else if t.isEmpty then .error (.invalidTicker "ticker must contain at least one character.")
  else if (Ticker.mk t).valid then .ok () else .error (.invalidTicker s!"invalid ticker {t}")

/-- `check_unicode_ticker` (BFA): 1 to 8 Unicode characters. -/
def checkUnicodeTicker (t : String) : Result Unit :=
  if t.length == 0 then .error (.invalidTicker "ticker must contain at least one character.")
  else if t.length > 8 then
    .error (.invalidTicker s!"ticker has {t.length} characters, while at most 8 are allowed.")
  else .ok ()

/-- `check_name`: printable ASCII, 1 to 40 chars. -/
def checkName (n : String) : Result Unit :=
  if (Name.mk n).valid then .ok () else .error (.invalidName s!"invalid name {n}")

/-- `check_details`: 1 to 255 UTF-8 bytes. -/
def checkDetails (d : String) : Result Unit :=
  if d.isEmpty then .error (.invalidDetails "ident must contain at least one character")
  else if (Details.mk d).valid then .ok () else .error (.invalidDetails "details too long")

/-- `check_precision`: 0 to 18. -/
def checkPrecision (p : Nat) : Result Precision :=
  match Precision.ofNat? p with
  | some x => .ok x
  | none => .error (.invalidPrecision "precision is too high")

def checkRejectListUrl (u : String) : Result Unit :=
  if (RejectListUrl.mk u).valid then .ok () else .error (.invalidRejectListUrl u)

/-- `check_contract_address`: `0x` then exactly 40 hex digits. -/
def checkContractAddress (a : String) : Result EvmAddress :=
  if !a.startsWith "0x" then .error (.invalidEvmContractAddress "address must start with 0x")
  else
    let h := (a.drop 2).toString
    if h.length != 40 || !h.toList.all (fun c => c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')) then
      .error (.invalidEvmContractAddress "address must be 20 hex-encoded bytes")
    else .ok ⟨Bytes.ofString (h.take 20).toString⟩

/-- `get_total_issue_amount`: at least one amount unless empty is allowed, none
zero, the sum fits `u64`. -/
def totalIssueAmount (amounts : List Nat) (allowEmpty : Bool := false) : Result Nat := do
  if amounts.isEmpty && !allowEmpty then throw .noIssuanceAmounts
  if amounts.contains 0 then throw .invalidAmountZero
  let s := amounts.sum
  if s > Bound.u64 then throw .tooHighIssuanceAmounts
  return s

/-- `get_total_inflation_amount`: none zero; the sum and `issued + sum` fit `u64`. -/
def totalInflationAmount (amounts : List Nat) (issued : Nat) : Result Nat := do
  if amounts.contains 0 then throw .invalidAmountZero
  let s := amounts.sum
  if s > Bound.u64 || issued + s > Bound.u64 then throw .tooHighInflationAmounts
  return s

namespace Wallet

def checkSchemaSupport (w : Wallet) (s : AssetSchema) : Result Unit :=
  if w.data.supportedSchemas.contains s then .ok () else .error (.unsupportedSchema s)

/-- Distinct UTXOs for the issued allocations: `true` asks for an empty UTXO. -/
def pickIssueUtxos (w : Wallet) (needsEmpty : List Bool) : Result (List DbTxo) := do
  let mut picked : List DbTxo := []
  for empty in needsEmpty do
    let t ← w.getUtxo (picked.map (·.outpoint)) false (if empty then some 0 else none)
    picked := picked ++ [t]
  return picked

/-- A linked-from contract must be known, of a schema with links, and not linked yet. -/
def checkLinkedFrom (w : Wallet) (id : String) : Result Unit := do
  let some a := w.db.asset? id | throw (.unknownLinkedContract id)
  if !a.schema.supportsLink then throw (.invalidLinkedContract id s!"schema {reprStr a.schema} doesn't support links")
  if let some to := a.linkedToContract then throw (.invalidLinkedContract id s!"it's already linked to contract {to}")

/-- Validate the genesis, import it, and record the issuance as a settled transfer. -/
def finalizeIssuance (w : Wallet) (now : Nat) (schema : AssetSchema) (g : Genesis)
    (allocs : List (DbTxo × Assignment)) (row : DbAsset) : Result (Wallet × DbAsset) := do
  let c : Consignment := { transfer := false, genesis := g }
  match c.validate false schema.rules .dumb { chainNet := w.chainNet } with
  | .error e => throw (.internal s!"invalid issuance: {reprStr e}")
  | .ok _ => pure ()
  let (ai, db) := w.db.fresh
  let (bi, db) := db.fresh
  let (ati, db) := db.fresh
  let (ti, db) := db.fresh
  let asset := { row with idx := ai }
  let batch : DbBatchTransfer :=
    { idx := bi, status := .settled, createdAt := now, updatedAt := now, minConfirmations := 0
      incoming := true }
  let mut db := { db with
    assets := db.assets ++ [asset]
    batchTransfers := db.batchTransfers ++ [batch]
    assetTransfers := db.assetTransfers ++ [⟨ati, true, bi, some row.id, none⟩]
    transfers := db.transfers ++ [{ idx := ti, assetTransferIdx := ati }] }
  for (t, a) in allocs do
    let (ci, d) := db.fresh
    db := { d with colorings := d.colorings ++ [⟨ci, t.idx, ati, .issue, a⟩] }
  db := { db with backupInfo := { db.backupInfo with lastOperation := now } }
  return ({ w with db, stock := w.stock.consumeGenesis g }, asset)

/-- Genesis seal on a UTXO with a blinding derived from the time and position. -/
def issueSeal (now : Nat) (i : Nat) (t : DbTxo) : BuilderSeal GenesisSeal :=
  .revealed ⟨t.outpoint.txid, t.outpoint.vout, (now * 1000 + i).toUInt64⟩

def baseGenesis (w : Wallet) (schema : Schema) (now : Nat) : Genesis :=
  { schemaId := schema.schemaId, timestamp := now, chainNet := w.chainNet }

def terms : ContractTerms := ⟨⟨""⟩, none⟩

/-- `issue_asset_nia(ticker, name, precision, amounts)`. -/
def issueAssetNia (w : Wallet) (now : Nat) (ticker name : String) (precision : Nat)
    (amounts : List Nat) : Result (Wallet × DbAsset) := do
  w.checkSchemaSupport .nia
  let total ← totalIssueAmount amounts
  checkTicker ticker
  checkName name
  let p ← checkPrecision precision
  let utxos ← w.pickIssueUtxos (amounts.map fun _ => false)
  let spec : AssetSpec := ⟨⟨ticker⟩, ⟨name⟩, none, p⟩
  let g := { w.baseGenesis Schemas.nia now with
    globals := OrdMap.ofList
      [ (Schemas.gsNominal, [⟨.assetSpec spec⟩]), (Schemas.gsTerms, [⟨.contractTerms terms⟩])
      , (Schemas.gsIssuedSupply, [⟨.amount total.toUInt64⟩]) ]
    assignments := OrdMap.ofList [(Schemas.osAsset, .fungible
      ((utxos.zip amounts).zipIdx.map fun ((t, a), i) => (issueSeal now i t, ⟨a.toUInt64⟩)))] }
  w.finalizeIssuance now .nia g (utxos.zip (amounts.map (.fungible ·.toUInt64)))
    { idx := 0, id := toString g.contractId, schema := .nia, addedAt := now, name, ticker := some ticker
      details := none, precision, initialSupply := total, timestamp := now }

/-- `issue_asset_cfa(name, details, precision, amounts)`. -/
def issueAssetCfa (w : Wallet) (now : Nat) (name : String) (details : Option String) (precision : Nat)
    (amounts : List Nat) : Result (Wallet × DbAsset) := do
  w.checkSchemaSupport .cfa
  let total ← totalIssueAmount amounts
  let p ← checkPrecision precision
  checkName name
  if let some d := details then checkDetails d
  let utxos ← w.pickIssueUtxos (amounts.map fun _ => false)
  let g := { w.baseGenesis Schemas.cfa now with
    globals := OrdMap.ofList
      ([ (Schemas.gsName, [⟨.name ⟨name⟩⟩]), (Schemas.gsPrecision, [⟨.precision p⟩])
       , (Schemas.gsTerms, [⟨.contractTerms terms⟩]), (Schemas.gsIssuedSupply, [⟨.amount total.toUInt64⟩]) ] ++
       (details.map fun d => (Schemas.gsDetails, [⟨.details ⟨d⟩⟩])).toList)
    assignments := OrdMap.ofList [(Schemas.osAsset, .fungible
      ((utxos.zip amounts).zipIdx.map fun ((t, a), i) => (issueSeal now i t, ⟨a.toUInt64⟩)))] }
  w.finalizeIssuance now .cfa g (utxos.zip (amounts.map (.fungible ·.toUInt64)))
    { idx := 0, id := toString g.contractId, schema := .cfa, addedAt := now, name, ticker := none
      details, precision, initialSupply := total, timestamp := now }

/-- `issue_asset_uda(ticker, name, details, precision, attachments)`: one token, index 0. -/
def issueAssetUda (w : Wallet) (now : Nat) (ticker name : String) (details : Option String)
    (precision : Nat) (attachments : Nat := 0) : Result (Wallet × DbAsset) := do
  w.checkSchemaSupport .uda
  if attachments > maxAttachments then throw (.invalidAttachments "no more than 20 attachments are supported")
  if let some d := details then checkDetails d
  checkTicker ticker
  checkName name
  let p ← checkPrecision precision
  let utxos ← w.pickIssueUtxos [false]
  let t := utxos.headD default
  let spec : AssetSpec := ⟨⟨ticker⟩, ⟨name⟩, details.map Details.mk, p⟩
  let g := { w.baseGenesis Schemas.uda now with
    globals := OrdMap.ofList
      [ (Schemas.gsNominal, [⟨.assetSpec spec⟩]), (Schemas.gsTerms, [⟨.contractTerms terms⟩])
      , (Schemas.gsTokens, [⟨.tokenData { index := ⟨0⟩ }⟩]) ]
    assignments := OrdMap.ofList [(Schemas.osAsset, .structured [(issueSeal now 0 t, ⟨.allocation ⟨0⟩ 1⟩)])] }
  w.finalizeIssuance now .uda g [(t, .nonFungible)]
    { idx := 0, id := toString g.contractId, schema := .uda, addedAt := now, name, ticker := some ticker
      details, precision, initialSupply := 1, timestamp := now }

/-- `issue_asset_ifa(...)`: issued amounts, inflation rights (max supply = issued
+ inflation), an optional reject list URL, link right and linked-from contract. -/
def issueAssetIfa (w : Wallet) (now : Nat) (ticker name : String) (precision : Nat)
    (amounts inflationAmounts : List Nat) (rejectListUrl : Option String := none)
    (linkRight : Bool := false) (linkedFrom : Option String := none) : Result (Wallet × DbAsset) := do
  w.checkSchemaSupport .ifa
  if let some l := linkedFrom then w.checkLinkedFrom l
  let issued ← totalIssueAmount amounts (allowEmpty := true)
  let infl ← totalInflationAmount inflationAmounts issued
  if issued == 0 && infl == 0 then throw .noIssuanceAmounts
  checkTicker ticker
  checkName name
  let p ← checkPrecision precision
  if let some u := rejectListUrl then checkRejectListUrl u
  let utxos ← w.pickIssueUtxos (amounts.map (fun _ => false) ++ inflationAmounts.map (fun _ => true) ++
    (if linkRight then [true] else []))
  let assetU := utxos.take amounts.length
  let inflU := (utxos.drop amounts.length).take inflationAmounts.length
  let linkU := utxos.drop (amounts.length + inflationAmounts.length)
  let spec : AssetSpec := ⟨⟨ticker⟩, ⟨name⟩, none, p⟩
  let g := { w.baseGenesis Schemas.ifa now with
    globals := OrdMap.ofList
      ([ (Schemas.gsNominal, [⟨.assetSpec spec⟩]), (Schemas.gsTerms, [⟨.contractTerms terms⟩])
       , (Schemas.gsIssuedSupply, [⟨.amount issued.toUInt64⟩])
       , (Schemas.gsMaxSupply, [⟨.amount (issued + infl).toUInt64⟩]) ] ++
       (rejectListUrl.map fun u => (Schemas.gsRejectListUrl, [⟨.rejectListUrl ⟨u⟩⟩])).toList ++
       (linkedFrom.map fun l => (Schemas.gsLinkedFromContract, [⟨.contractId (Digest.of "asset-id" [l])⟩])).toList)
    assignments := OrdMap.ofList
      ((if amounts.isEmpty then [] else [(Schemas.osAsset, .fungible
          ((assetU.zip amounts).zipIdx.map fun ((t, a), i) => (issueSeal now i t, ⟨a.toUInt64⟩)))]) ++
       (if inflationAmounts.isEmpty then [] else [(Schemas.osInflation, .fungible
          ((inflU.zip inflationAmounts).zipIdx.map fun ((t, a), i) => (issueSeal now (100 + i) t, ⟨a.toUInt64⟩)))]) ++
       (if linkRight then [(Schemas.osLink, .declarative (linkU.zipIdx.map fun (t, i) => issueSeal now (200 + i) t))]
        else [])) }
  let allocs := assetU.zip (amounts.map (.fungible ·.toUInt64)) ++
    inflU.zip (inflationAmounts.map (.inflationRight ·.toUInt64)) ++ linkU.map (·, .linkRight)
  let (w, a) ← w.finalizeIssuance now .ifa g allocs
    { idx := 0, id := toString g.contractId, schema := .ifa, addedAt := now, name, ticker := some ticker
      details := none, precision, initialSupply := issued, maxSupply := some (issued + infl)
      knownCirculatingSupply := some issued, timestamp := now
      rejectList := rejectListUrl.map (.url ⟨·⟩), linkedFromContract := linkedFrom }
  return (w, a)

/-- `issue_asset_bfa(...)`: mint rights on empty UTXOs, the bridge contract, an
optional EVM reject list on the same chain, link right and linked-from contract. -/
def issueAssetBfa (w : Wallet) (now : Nat) (ticker name : String) (precision : Nat) (mintRights : Nat)
    (chainId : Nat) (contractAddress : String) (rejectListAddress : Option String := none)
    (linkRight : Bool := false) (linkedFrom : Option String := none) : Result (Wallet × DbAsset) := do
  w.checkSchemaSupport .bfa
  if let some l := linkedFrom then w.checkLinkedFrom l
  if mintRights == 0 then throw .noMintRights
  checkUnicodeTicker ticker
  let addr ← checkContractAddress contractAddress
  checkName name
  let p ← checkPrecision precision
  let rl ← match rejectListAddress with
    | some a => (checkContractAddress a).map (some ·)
    | none => pure none
  let utxos ← w.pickIssueUtxos ((List.replicate mintRights true) ++ (if linkRight then [true] else []))
  let mintU := utxos.take mintRights
  let linkU := utxos.drop mintRights
  let bridge : EvmContract := ⟨chainId.toUInt64, addr⟩
  let g := { w.baseGenesis Schemas.bfa now with
    globals := OrdMap.ofList
      ([ (Schemas.gsTicker, [⟨.unicodeTicker ⟨ticker⟩⟩]), (Schemas.gsName, [⟨.name ⟨name⟩⟩])
       , (Schemas.gsPrecision, [⟨.precision p⟩]), (Schemas.gsTerms, [⟨.contractTerms terms⟩])
       , (Schemas.gsBridgeLocation, [⟨.bridgeLocation (.evm bridge)⟩]) ] ++
       (rl.map fun a => (Schemas.gsRejectList, [⟨.rejectListLocation (.evm ⟨chainId.toUInt64, a⟩)⟩])).toList ++
       (linkedFrom.map fun l => (Schemas.gsLinkedFromContract, [⟨.contractId (Digest.of "asset-id" [l])⟩])).toList)
    assignments := OrdMap.ofList
      ([(Schemas.osMint, .declarative (mintU.zipIdx.map fun (t, i) => issueSeal now i t))] ++
       (if linkRight then [(Schemas.osLink, .declarative (linkU.zipIdx.map fun (t, i) => issueSeal now (200 + i) t))]
        else [])) }
  w.finalizeIssuance now .bfa g (mintU.map (·, .mintRight) ++ linkU.map (·, .linkRight))
    { idx := 0, id := toString g.contractId, schema := .bfa, addedAt := now, name, ticker := some ticker
      details := none, precision, initialSupply := 0, timestamp := now
      rejectList := rl.map fun a => .evm ⟨chainId.toUInt64, a⟩, bridgeLocation := some (.evm bridge)
      linkedFromContract := linkedFrom }

end Wallet

end Rgb.Lib
