import Rgb.Lib.Enums

/-!
# rgb-lib errors

Every error the wallet library returns (`rgb_lib::Error`), with the condition
that raises it. Five variants are never raised (`failedIssuance`,
`invalidElectrum`, `invalidVanillaKeychain`, `noKeysSupplied`,
`recipientIdAlreadyUsed`); they stay for the bindings.
-/

namespace Rgb.Lib

inductive Error where
  /-- `create_utxos` with `up_to` while enough free UTXOs exist. -/
  | allocationsAlreadyAvailable
  /-- `import_contract` of an asset already in the wallet. -/
  | assetAlreadyKnown (assetId : String)
  /-- An asset id unknown to the wallet. -/
  | assetNotFound (assetId : String)
  | batchTransferNotFound (idx : Nat)
  /-- Wallet data or BDK state of another network. -/
  | bitcoinNetworkMismatch
  | cannotAbortPendingVanillaTx
  /-- An `Online` object of another session. -/
  | cannotChangeOnline
  | cannotCombinePsbts
  /-- Only failed transfers can be deleted (and not those of a live reusable invoice). -/
  | cannotDeleteBatchTransfer
  /-- `_end` of an operation not in a status that can end. -/
  | cannotEndTransfer (txid : String)
  | cannotEstimateFees
  | cannotFailBatchTransfer
  | cannotFinalizePsbt
  | cannotLinkToItself
  | cannotProvideOutOfBandAck (details : String)
  | cannotProvideOutOfBandConsignment (details : String)
  | cannotReuseAddress (details : String)
  /-- IFA and BFA on mainnet without `allow_reckless_schemas`. -/
  | cannotUseSchemaOnMainnet (schema : AssetSchema)
  /-- A reject list rejects these opouts of the consignment's history. -/
  | consignmentRejected (opouts : List String)
  | consignmentValidationFailed (details : String)
  | database (details : String)
  | duplicateProxyAuthKey (details : String)
  | emptyFile (filePath : String)
  | evmChainIdMismatch (expected actual : Nat)
  /-- An expiration the proxy refuses. -/
  | expirationInvalid
  | failedBdkSync (details : String)
  | failedBroadcast (details : String)
  | failedIssuance (details : String)
  | fileAlreadyExists (path : String)
  | fileTooLarge (filePath : String) (maxSize : Nat)
  | fingerprintMismatch
  | hashMismatch
  | io (details : String)
  /-- The UTXO set changed behind the wallet's back. -/
  | inconsistency (details : String)
  | indexer (details : String)
  | inexistentDataDir
  | inexistentWalletManifest (path : String)
  /-- No UTXO has a free allocation slot. -/
  | insufficientAllocationSlots
  /-- The wallet holds less of the asset than the operation needs. -/
  | insufficientAssignments (assetId : String) (available : Nat)
  | insufficientBitcoins (needed available : Nat)
  | internal (details : String)
  | invalidAddress (details : String)
  | invalidAmountZero
  | invalidAssignment
  | invalidAttachments (details : String)
  | invalidBeforeBlock (details : String)
  | invalidBitcoinKeys
  | invalidBitcoinNetwork (network : String)
  | invalidBurnReason (details : String)
  | invalidColoringInfo (details : String)
  | invalidConsignment
  | invalidContentSignature
  | invalidContract (filePath : String)
  | invalidContractId (contractId : String)
  | invalidCosigner (details : String)
  | invalidDetails (details : String)
  | invalidElectrum (details : String)
  | invalidEncryptedBlob (details : String)
  | invalidEndpointAuthSignature
  | invalidEstimationBlocks
  | invalidEvmChain (details : String)
  | invalidEvmContractAddress (details : String)
  | invalidEvmRpcUrl (details : String)
  | invalidExpiration
  | invalidFeeRate (details : String)
  | invalidFilePath (filePath : String)
  | invalidFingerprint
  | invalidIndexer (details : String)
  | invalidInvoice (details : String)
  | invalidLinkedContract (contractId details : String)
  | invalidMnemonic (details : String)
  | invalidMultisigThreshold (required total : Nat)
  | invalidName (details : String)
  | invalidPrecision (details : String)
  | invalidProxyAuthKey (details : String)
  | invalidProxyAuthSignature
  | invalidProxyProtocol (version : String)
  | invalidPsbt (details : String)
  | invalidPubkey (details : String)
  | invalidQuota (details : String)
  | invalidRecipientData (details : String)
  | invalidRecipientId
  | invalidRecipientMap
  | invalidRecipientNetwork
  | invalidRejectList (details : String)
  | invalidRejectListUrl (details : String)
  | invalidTicker (details : String)
  | invalidTransportEndpoint (details : String)
  | invalidTransportEndpoints (details : String)
  | invalidTxid
  | invalidVanillaKeychain
  | invalidWitnessVersion (witnessVersion : String)
  | invoiceExpired
  | invoiceNotReserved
  | invoiceQuotaExceeded
  /-- A mint would spend the wallet's last mint right of the asset. -/
  | lastMintRight
  | maxFeeExceeded (txid : String)
  | minFeeNotMet (txid : String)
  /-- The bridge lock of a mint can no longer be recorded in time. -/
  | mintLockExpired (opid : String) (beforeBlock : Nat)
  /-- The bridge lock of a mint is not finalized (yet). -/
  | mintLockNotFound (opid : String)
  | multisigCannotMarkOperationProcessed (details : String)
  | multisigCannotRespondToOperation (details : String)
  | multisigHubService (details : String)
  | multisigLegacyOperation (operationIdx : Nat)
  | multisigOperationInProgress
  | multisigOperationNotFound (operationIdx : Nat)
  | multisigTransferStatusMismatch
  | multisigUnexpectedData (details : String)
  | multisigUserNotCosigner
  | network (details : String)
  | noBurnAmount
  | noClaimResolver
  | noConsignment
  | noCosignersSupplied
  | noEvmRpcUrl (chainId : Nat)
  | noInflationAmounts
  | noIssuanceAmounts
  | noKeysSupplied
  | noMaxAllocationsPerUtxo
  | noMedia
  | noMintRights
  | noRejectListResolver
  | noSupportedSchemas
  | noValidTransportEndpoint
  | offchainTxidNotFound (txid : String)
  | offline
  | onlineNeeded
  | operationExpired
  | operationNotFound
  | outputBelowDustLimit
  | proxy (details : String)
  | proxyCannotChange (details : String)
  | proxyDraining
  | proxyTooManyMedia
  | proxyTxAlreadyReleased
  | psbtInspection (details : String)
  | recipientIdAlreadyUsed
  | recipientIdDuplicated
  | rejectListService (details : String)
  | restClientBuild (details : String)
  | rgbInspection (details : String)
  | signedTxCleared
  | tooHighInflationAmounts
  | tooHighIssuanceAmounts
  | tooManyCosigners
  | tooManySignaturesInPsbt
  | transferIdDeleted
  | transferIdInUse
  | unknownLinkedContract (contractId : String)
  | unknownRgbSchema (schemaId : String)
  | unknownTransfer (txid : String)
  | unsupportedAddressReuse (details : String)
  | unsupportedBackupVersion (version : String)
  | unsupportedBurn (schema : AssetSchema)
  | unsupportedInflation (schema : AssetSchema)
  | unsupportedLayer1 (layer1 : String)
  | unsupportedLink (schema : AssetSchema)
  | unsupportedMint (schema : AssetSchema)
  | unsupportedSchema (schema : AssetSchema)
  | unsupportedTransportType
  | unsupportedWalletManifestVersion (version : String)
  | walletDirAlreadyExists (path : String)
  | walletSettingMismatch (setting expected provided : String)
  /-- An all-in-one operation that needs signing on a watch-only wallet. -/
  | watchOnly
  | wrongOperation (txid : String)
  | wrongPassword
  deriving DecidableEq, Repr, Inhabited

/-- Wallet results. -/
abbrev Result (α : Type) := Except Error α

end Rgb.Lib
