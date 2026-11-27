import Rgb.Lib.Refresh

/-!
# Contracts, fees and PSBTs

`import_contract` adds a contract the wallet holds no state of (validated with
the wallet's network, refused when already known), `export_contract` writes the
genesis-only consignment of a known asset. `get_fee_estimation` reads the
indexer's estimate for a target in blocks. In the model a PSBT is its unsigned
transaction: signing and finalizing check what rgb-lib checks and return it.
-/

namespace Rgb.Lib

namespace Wallet

/-- Import a contract consignment (`import_contract`). -/
def importContract (w : Wallet) (now : Nat) (c : Consignment) (size : Nat := 0) : Result Wallet := do
  if size > maxContractSize then throw (.fileTooLarge "contract" maxContractSize)
  if c.transfer then throw (.invalidContract "contract")
  let some schema := AssetSchema.ofSchemaId? c.schemaId
    | throw (.unknownRgbSchema (toString c.schemaId))
  w.checkSchemaSupport schema
  let id := toString c.contractId
  if (w.db.asset? id).isSome then throw (.assetAlreadyKnown id)
  match c.validate false schema.rules .dumb { chainNet := w.chainNet } with
  | .error e => throw (.consignmentValidationFailed (reprStr e))
  | .ok _ => pure ()
  let (ai, db) := w.db.fresh
  let row := assetRowOf schema c.genesis now
  return { w with db := { db with assets := db.assets ++ [{ row with idx := ai }] }
                  stock := w.stock.consumeGenesis c.genesis }

/-- The genesis-only consignment of a known asset (`export_contract`). -/
def exportContract (w : Wallet) (assetId : String) : Result Consignment := do
  let _ ← w.asset? assetId
  let some cid := w.contractIdOf? assetId | throw (.assetNotFound assetId)
  (w.stock.exportContract cid).mapError fun e => .internal (reprStr e)

/-- Fee estimate for confirmation within `blocks` (`get_fee_estimation`), from
the indexer's map of targets to sat/vB: an exact target, or linear
interpolation between the nearest targets around it. -/
def feeEstimation (estimates : List (Nat × Nat)) (blocks : Nat) : Result Nat := do
  if blocks < minBlockEstimation || blocks > maxBlockEstimation then throw .invalidEstimationBlocks
  if estimates.isEmpty then throw .cannotEstimateFees
  match estimates.find? (·.1 == blocks) with
  | some (_, v) => return v
  | none =>
    let lower := (estimates.filter (·.1 < blocks)).foldl (fun acc e => match acc with
      | some a => if e.1 > a.1 then some e else acc
      | none => some e) none
    let upper := (estimates.filter (·.1 > blocks)).foldl (fun acc e => match acc with
      | some a => if e.1 < a.1 then some e else acc
      | none => some e) none
    match lower, upper with
    | some (x1, y1), some (x2, y2) =>
      return if y2 ≥ y1 then y1 + (blocks - x1) * (y2 - y1) / (x2 - x1)
        else y1 - (blocks - x1) * (y1 - y2) / (x2 - x1)
    | _, _ => throw (.internal "esplora map doesn't contain the expected keys")

/-- Sign a PSBT (`sign_psbt`); a watch-only wallet returns it unsigned. -/
def signPsbt (_w : Wallet) (tx : Tx) : Result Tx := .ok tx

/-- Finalize a PSBT (`finalize_psbt`): it must spend something. -/
def finalizePsbt (tx : Tx) : Result Tx :=
  if tx.inputs.isEmpty then .error .cannotFinalizePsbt else .ok tx

end Wallet

end Rgb.Lib
