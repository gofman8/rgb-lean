/-!
# rgb-lib constants

Limits, defaults and timing constants of the wallet library.
-/

namespace Rgb.Lib

/-! ## Limits and defaults -/

/-- Furthest invoice or operation expiration, in seconds from now (ten years). -/
def maxExpirationSecs : Nat := 10 * 365 * 24 * 60 * 60
/-- Clock skew tolerated between the wallet and a proxy, and the least lead of an
operation expiration over now. -/
def proxyClockSkewMarginSecs : Nat := 300
/-- An operation must expire this long before the earliest invoice it pays expires. -/
def invoiceExpirationMarginSecs : Nat := 2 * proxyClockSkewMarginSecs
/-- A recipient refuses a sender proxy that keeps data for less than this. -/
def minSenderRetentionGraceSecs : Nat := 86400
/-- A recipient waits this long after the broadcast deadline before failing. -/
def confirmationMarginSecs : Nat := 86400
/-- Most proof-of-work bits the wallet computes to post a consignment. -/
def maxPowDifficulty : Nat := 28
/-- Most attachments of a UDA token. -/
def maxAttachments : Nat := 20
/-- Most transport endpoints of a receive or a recipient. -/
def maxTransportEndpoints : Nat := 3
/-- Token index of every UDA the wallet issues. -/
def udaFixedIndex : Nat := 0
/-- Prefix of asset ids. -/
def assetIdPrefix : String := "rgb:"
/-- Most allocations of one asset a UTXO can hold and still be spent (bundle input map bound). -/
def maxUtxoAssetAllocations : Nat := 65535
/-- Largest contract file `import_contract` accepts (16 MiB). -/
def maxContractSize : Nat := 16 * 1024 * 1024
/-- Default number of UTXOs `create_utxos` makes. -/
def utxoNum : Nat := 5
/-- Default size of each created UTXO, in sats. -/
def utxoSize : Nat := 1000
/-- Lowest fee rate, in sat/vB. -/
def minFeeRate : Nat := 1
/-- Highest fee rate: `fee_rate * 250` must fit in `u64`. -/
def maxFeeRate : Nat := 18446744073709551615 / 250
/-- Valid target blocks for fee estimation. -/
def minBlockEstimation : Nat := 1
def maxBlockEstimation : Nat := 1008
/-- Number of asset schemas rgb-lib knows. -/
def numKnownSchemas : Nat := 5
/-- Only wallet manifest version accepted by `load`. -/
def walletManifestVersion : Nat := 1
/-- Only backup version accepted by `restore_backup`. -/
def backupVersion : Nat := 1
/-- Only RGB proxy protocol version accepted. -/
def proxyProtocolVersion : String := "1.0"

/-! ## Key derivation -/

/-- BIP purpose of the multisig account path. -/
def purposeMultisig : Nat := 86
/-- Colored coin type on mainnet and on every other network. -/
def coinRgbMainnet : Nat := 827166
def coinRgbTestnet : Nat := 827167
/-- Hardened account index. -/
def account : Nat := 0
/-- Colored and default vanilla keychain indexes. -/
def keychainRgb : Nat := 0
def keychainBtc : Nat := 0

/-! ## Backup encryption -/

def backupKeyLength : Nat := 32
def backupNonceLength : Nat := 19
/-- scrypt parameters of the backup key: `log_n`, `r`, `p`. -/
def scryptLogN : Nat := 17
def scryptR : Nat := 8
def scryptP : Nat := 1

end Rgb.Lib
