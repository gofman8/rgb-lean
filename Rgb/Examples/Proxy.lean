import Rgb.Lib.Proxy

/-!
# Proxy protocol scenarios

The cryptography of the proxy protocol (shared keys, identifiers, encrypted blobs, proof of work),
the mapping of every error code, and transfers through a proxy: a recipient reserves an invoice, a
sender registers its operation and posts a consignment, the recipient downloads and ACKs it and
gets the signed transaction back. Variants show a batch released on its last ACK, a NACK, a
revoked operation, an expired invoice, the quota, the retention grace, a draining proxy and the
authenticated calls. The proxy reads neither the consignment nor the transaction, so a contract
consignment and a plain witness transaction stand for them.
-/

namespace Rgb.Examples.Proxy

open Rgb Rgb.Lib Rgb.Lib.ProxyCrypto Rgb.Lib.Proxy

/-- The value of a step that must succeed (the default otherwise, which fails the checks after). -/
def ok! {ε α : Type} [Inhabited α] : Except ε α → α
  | .ok a => a
  | .error _ => default

/-- `n` copies of `c`. -/
def rep (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

def alice : SecretKey := ⟨"alice"⟩
def bob : SecretKey := ⟨"bob"⟩
def carol : SecretKey := ⟨"carol"⟩
def dave : SecretKey := ⟨"dave"⟩

/-! ## Keys and signatures -/

-- both parties derive the same keys
#guard deriveShared alice bob.pk == deriveShared bob alice.pk
#guard [alice, bob, carol, dave].all fun a =>
  [alice, bob, carol, dave].all fun b => deriveShared a b.pk == deriveShared b a.pk
-- another counterparty gives other keys and another seal blinding
#guard (deriveShared alice bob.pk).symKey != (deriveShared alice carol.pk).symKey
#guard (deriveShared alice bob.pk).sealBlinding != (deriveShared alice carol.pk).sealBlinding
#guard (deriveShared alice bob.pk).symKey != (deriveShared alice bob.pk).kmid
-- media ids agree on both sides
#guard (deriveShared alice bob.pk).mediaId (rep '7' 64)
  == (deriveShared bob alice.pk).mediaId (rep '7' 64)
-- public keys are 32 bytes in hex
#guard isPubkeyHex alice.pk && !isPubkeyHex (alice.pk ++ "00") && !isPubkeyHex (rep 'z' 64)
-- a signature verifies exactly for its signer's key and message
#guard verifyMessage alice.pk "rgb-proxy ack message" (signMessage alice "rgb-proxy ack message")
#guard !verifyMessage alice.pk "other" (signMessage alice "rgb-proxy ack message")
#guard !verifyMessage bob.pk "rgb-proxy ack message" (signMessage alice "rgb-proxy ack message")

/-! ## Identifiers -/

def ridA : String := "bcrt:utxob:alice-seal"
def iidA : String := invoiceId ridA alice.pk
def tidA : String := transferId iidA bob.pk

-- `invoice_id` and `transfer_id` hash their prefix and parts
#guard iidA == sha256Hex ("rgb-proxy-server/invoice/v1" ++ ridA ++ alice.pk)
#guard tidA == sha256Hex ("rgb-proxy-server/transfer/v1" ++ iidA ++ bob.pk)
#guard isTransferId tidA && isTransferId iidA
-- the recipient key and the sender key are part of the ids
#guard iidA != invoiceId ridA carol.pk && tidA != transferId iidA carol.pk
-- anything else than a hex digest is not a transfer id
#guard ["", "abc", rep '0' 63, rep '0' 65, rep 'A' 64, rep '0' 61 ++ "/..", rep '0' 62 ++ "é"].all
  (!isTransferId ·)

/-! ## Encrypted blobs -/

-- one chunk per started 64 KiB, at least one
#guard [0, 1, 65535, 65536, 65537, 131072, 204800].map chunkCount == [1, 1, 1, 1, 2, 2, 4]
-- the version byte, the plaintext and one tag per chunk
#guard [0, 1, 100, 65535, 65536, 65537, 131072, 204800].map sealedLen
  == [17, 18, 117, 65552, 65553, 65570, 131105, 204865]

/-- A contract consignment: a genesis on regtest. -/
def consignment : Consignment :=
  { transfer := false
    genesis := { schemaId := ⟨Digest.of Tag.schema ["NIA"]⟩, timestamp := 1713261744
                 chainNet := .bitcoinRegtest } }
/-- The signed transaction: an `OP_RETURN` output for the commitment, then two payments. -/
def tx : Tx :=
  { inputs := [⟨⟨⟨Digest.of Tag.txid ["funding"]⟩, 0⟩, 0xFFFFFFFD⟩]
    outputs := [⟨0, .opReturn none⟩, ⟨546, .p2wpkh "alice"⟩, ⟨9000, .p2wpkh "bob"⟩] }
def cP : Payload := .consignment consignment
def txP : Payload := .tx tx
/-- `consignment_hash` of the consignment. -/
def ch : String := cP.hash
/-- `signed_tx_hash` of the transaction. -/
def txHash : String := txP.hash
/-- What bob, as sender, and alice, as recipient, derive. -/
def keysAB : DerivedKeys := deriveShared bob alice.pk
def key : String := keysAB.symKey
def bytesOf (n : Nat) : Payload := .bytes (rep 'x' n)

#guard [0, 1, 65536, 65537].all fun n =>
  (bytesOf n).len == n && (Blob.encrypt (bytesOf n) key).len == sealedLen n
#guard (Blob.encrypt cP key).len == sealedLen cP.len
-- a blob opens with its key and plaintext hash
#guard [0, 1, 65536, 65537].all fun n =>
  (Blob.encrypt (bytesOf n) key).decrypt key (bytesOf n).hash == .ok (bytesOf n)
#guard (Blob.encrypt cP key).decrypt key ch == .ok cP

def sealedTx : Sealed := { key, plainHash := txHash, payload := txP }
def big : Sealed :=
  { key, plainHash := (bytesOf (chunkSize + 10)).hash, payload := bytesOf (chunkSize + 10) }
def failed (msg : String) : Except Error Payload := .error (.invalidEncryptedBlob msg)

#guard (Blob.sealed sealedTx).decrypt key txHash == .ok txP
-- another key, another plaintext hash (another nonce base) or a changed byte fail authentication
#guard (Blob.sealed sealedTx).decrypt (deriveShared bob carol.pk).symKey txHash
  == failed "authentication failed"
#guard (Blob.sealed sealedTx).decrypt key ch == failed "authentication failed"
#guard (Blob.tampered sealedTx).decrypt key txHash == failed "authentication failed"
-- another format version is refused first
#guard (Blob.sealed { sealedTx with version := 2 }).decrypt key txHash
  == failed "unsupported encryption version 2"
-- truncation: nothing, less than a tag, or a body that no longer opens
#guard (Blob.cut sealedTx 0).decrypt key txHash == failed "empty encrypted blob"
#guard (Blob.cut sealedTx 16).decrypt key txHash == failed "truncated encrypted blob"
#guard (Blob.cut sealedTx 17).decrypt key txHash == failed "authentication failed"
#guard (Blob.cut sealedTx (sealedTx.len - 1)).decrypt key txHash == failed "authentication failed"
#guard (Blob.cut sealedTx sealedTx.len).decrypt key txHash == .ok txP
-- two chunks: cut right after the first, now final, or inside the last leaving less than a tag
#guard (Blob.cut big (1 + encChunkSize)).decrypt key big.plainHash == failed "authentication failed"
#guard (Blob.cut big (1 + encChunkSize + tagLen - 1)).decrypt key big.plainHash
  == failed "truncated encrypted blob"
#guard (Blob.cut big (big.len - 1)).decrypt key big.plainHash == failed "authentication failed"
-- files never encrypted: their first byte is not the format version
#guard (Blob.plain cP).decrypt key ch == failed "unsupported encryption version 82"
#guard (Blob.plain txP).decrypt key txHash == failed "unsupported encryption version 2"
#guard (Blob.plain (.bytes "")).decrypt key "" == failed "empty encrypted blob"
#guard (Blob.plain (.bytes "\x01short")).decrypt key "" == failed "truncated encrypted blob"
-- how a receiver reads a download, by the encryption it asked for
#guard (Blob.plain cP).decryptWith .unsupported key ch == .ok cP
#guard (Blob.plain cP).decryptWith .optional key ch == .ok cP
#guard (Blob.plain cP).decryptWith .required key ch == failed "unsupported encryption version 82"
#guard (Blob.encrypt cP key).decryptWith .optional key ch == .ok cP
#guard (Blob.encrypt cP key).decryptWith .required key ch == .ok cP
-- bytes read as they are must hash to the announced plaintext hash
#guard (Blob.encrypt cP key).decryptWith .unsupported key ch == .error .hashMismatch
#guard (Blob.encrypt cP key).decryptWith .optional (deriveShared alice carol.pk).symKey ch
  == .error .hashMismatch
#guard (Blob.plain cP).decryptWith .optional key txHash == .error .hashMismatch

/-! ## Proof of work -/

#guard leadingZeroBits [0xff] == 0 && leadingZeroBits [0x01] == 7
#guard leadingZeroBits [0x00, 0x00, 0x10] == 19 && leadingZeroBits [0x00, 0x00] == 16
#guard solvePow "tid" "123" 0 == "0"
#guard [1, 4, 8, 12].all fun d => powMeets "tid" "123" (solvePow "tid" "123" d) d
-- the least such nonce
#guard [4, 8].all fun d =>
  (List.range (solvePowNonce "tid" "123" d)).all fun n => !powMeets "tid" "123" (toString n) d

/-! ## Signed messages and methods -/

#guard Msg.postConsignment "t" "c" "b" == "tcbconsignment"
#guard Msg.postMedia "t" "m" "b" == "tmbmedia"
#guard Msg.getAck ["b", "c", "a"] "9" == "abc9" && Msg.cleanAck ["b", "a"] == "ab"
#guard Msg.ack "t" true "h" == "ttrueh" && Msg.ack "t" false "h" == "tfalseh"
#guard Msg.listTransfers "i" "9" == "i9"
#guard Msg.transferRetrieved "t" == "tretrieved" && Msg.deleteTransfer "t" == "tdelete"
#guard Msg.prepareInvoiceAuth "i" "9" "pk" 2 == "i9pk2"
#guard Msg.prepareAckAuth "s" "9" "h" [("t2", ⟨"p2", "c2", default⟩), ("t1", ⟨"p1", "c1", default⟩)]
  == "s9ht1p1c1t2p2c2"
#guard Method.all.length == 14 && (Method.all.map (·.name)).eraseDups.length == 14
#guard Method.all.filter (·.uploadsFile) == [.consignmentPost, .mediaPost, .ackPrepare]
#guard Method.all.filter (·.startsTransfer) == [.invoicePrepare, .consignmentPost, .ackPrepare]
#guard (Method.all.filter (·.signer? == some .sender)).map (·.name)
  == ["consignment.post", "media.post", "ack.get", "ack.clean"]
#guard (Method.all.filter (·.signer? == some .recipient)).map (·.name)
  == ["transfer.list", "transfer.retrieved", "transfer.delete", "ack.post"]

/-! ## Error codes -/

def rpcErr (code : Int) (fields : List String := []) : JsonRpcError :=
  { code, message := "msg", fields }

-- -100: a cleared signed TX when it is the only field, a refused change otherwise
#guard mapProxyError (rpcErr (-100) ["signed_tx"]) == .signedTxCleared
#guard mapProxyError (rpcErr (-100) ["sender_pk"]) == .proxyCannotChange "msg: sender_pk"
#guard mapProxyError (rpcErr (-100) ["signed_tx", "sender_pk"])
  == .proxyCannotChange "msg: signed_tx, sender_pk"
#guard mapProxyError (rpcErr (-100)) == .proxyCannotChange "msg"
-- -200: an invalid expiration when `expires_at` is among the fields
#guard mapProxyError (rpcErr (-200) ["expires_at"]) == .expirationInvalid
#guard mapProxyError (rpcErr (-200) ["invoice_id", "expires_at"]) == .expirationInvalid
#guard mapProxyError (rpcErr (-200) ["signature"]) == .proxy "msg: signature"
#guard mapProxyError (rpcErr (-200)) == .proxy "msg"
-- a missing `expires_at` is not an invalid one
#guard mapProxyError (rpcErr (-300) ["expires_at"]) == .proxy "msg: expires_at"
#guard mapProxyError (rpcErr (-301)) == .proxy "msg"
-- -114 keeps its details; the client reads the difficulty from its data
#guard mapProxyError { rpcErr (-114) with powDifficulty := some "12" } == .proxy "msg"
#guard powDifficultyRequired { rpcErr (-114) with powDifficulty := some "12" } == some 12
#guard powDifficultyRequired { rpcErr (-200) with powDifficulty := some "12" } == none
#guard powDifficultyRequired (rpcErr (-114)) == none
#guard powDifficultyRequired { rpcErr (-114) with powDifficulty := some "x" } == none
-- the codes with one wallet error each, whatever their data
def codeTable : List (Int × Error) :=
  [(-101, .invoiceNotReserved), (-102, .transferIdInUse), (-104, .operationNotFound),
    (-105, .operationExpired), (-107, .proxyTxAlreadyReleased), (-111, .invoiceExpired),
    (-112, .invoiceQuotaExceeded), (-113, .transferIdDeleted), (-115, .proxyDraining),
    (-116, .proxyTooManyMedia), (-400, .noConsignment), (-401, .noMedia), (-402, .noConsignment),
    (-403, .noConsignment), (-501, .invalidProxyAuthSignature),
    (-502, .invalidEndpointAuthSignature), (-503, .invalidContentSignature)]
#guard codeTable.all fun (c, e) =>
  mapProxyError (rpcErr c) == e && mapProxyError (rpcErr c ["x"]) == e
#guard codeErrors == codeTable
-- any other code is a generic proxy error
#guard [-103, -106, -108, -110, -117, -201, -404, -500, -504, -32601].all fun c =>
  mapProxyError (rpcErr c) == .proxy "msg"

/-! ## Reading proxy answers -/

def t0 : Nat := 1700000000
def url : String := "http://proxy.test/json-rpc"
def endpoint : String := "rpc://proxy.test/json-rpc"
def s0 : Server := Server.init url t0

#guard s0.checkProxy == .ok s0.info && s0.info.protocolVersion == "1.0"
#guard checkProxy { result := some { s0.info with protocolVersion := "0.2" } }
  == .error (.invalidProxyProtocol "0.2")
#guard checkProxy { error := some { code := -32601, message := "Method not found" } }
  == .error (.proxy "Method not found")
#guard checkProxy {} == .error (.proxy "proxy response has neither result nor error")
-- the retention grace a proxy advertises; none or an unreadable one is 0
#guard proxyRetentionGrace s0.info == 86400
#guard proxyRetentionGrace (Server.init url t0 3600).info == 3600
#guard proxyRetentionGrace { s0.info with retentionGraceSecs := none } == 0
#guard proxyRetentionGrace { s0.info with retentionGraceSecs := some "one day" } == 0
#guard proxyRetentionGrace { s0.info with retentionGraceSecs := some "4294967296" } == 0
#guard senderProxyRetentionGrace s0.serverInfo == .ok 86400
#guard senderProxyRetentionGrace {} == .error (.proxy "missing server.info result")
#guard senderProxyRetentionGrace { error := some (Err.code Code.draining) } == .error .proxyDraining
#guard proxyMaxMedia s0.info == some defaultMaxMedia
#guard proxyMaxMedia { s0.info with maxMedia := none } == none
-- what `ack.clean` and `ack.get` answers mean to the sender
#guard cleanAckOutcome none == .ok .revoked
#guard cleanAckOutcome (some .proxyTxAlreadyReleased) == .ok .released
#guard cleanAckOutcome (some .operationNotFound) == .ok .unknown
#guard cleanAckOutcome (some .invalidEndpointAuthSignature) == .error .invalidEndpointAuthSignature
#guard checkGetAckError .operationNotFound == .ok ()
#guard checkGetAckError .invalidContentSignature == .error .invalidContentSignature
#guard senderProxyKnowsOperation none == .ok true
#guard senderProxyKnowsOperation (some .operationNotFound) == .ok false
#guard senderProxyKnowsOperation (some .proxyDraining) == .error .proxyDraining
#guard parseI64? "-5" == some (-5) && parseI64? "+5" == some 5 && parseI64? "" == none
#guard parseUnsigned? "+7" 32 == some 7 && parseUnsigned? "-7" 32 == none
#guard parseUnsigned? "4294967295" 32 == some 4294967295 && parseUnsigned? "4294967296" 32 == none
-- the clock advances
#guard (s0.tick 60).info.currentTime == some (toString (t0 + 60)) && (s0.tick 60).info.uptime == 60

/-! ## A transfer to one recipient -/

def invoiceExp : Nat := t0 + 3 * 86400
def opExp : Nat := t0 + 2 * 86400

-- the recipient reserves its invoice on the proxy
def s1 : Server := ok! (s0.invoicePrepare iidA invoiceExp alice.pk 1)
#guard s0.invoiceCheck [iidA] == [(iidA, .unknown)]
#guard s1.invoiceCheck [iidA] == [(iidA, .available)]
-- the same reservation again changes nothing; another one is refused
#guard s1.invoicePrepare iidA invoiceExp alice.pk 1 == .ok s1
#guard s1.invoicePrepare iidA invoiceExp alice.pk 2
  == .error (.proxyCannotChange "Cannot change: quota")
-- an expiration in the past or beyond the proxy's furthest one, and quotas out of range
#guard s0.invoicePrepare iidA (t0 - 1) alice.pk 1 == .error .expirationInvalid
#guard s0.invoicePrepare iidA (t0 + defaultMaxExpirySecs + 1) alice.pk 1
  == .error .expirationInvalid
#guard s0.invoicePrepare iidA invoiceExp alice.pk 0 == .error (.proxy "Invalid: quota")
#guard s0.invoicePrepare iidA invoiceExp alice.pk (defaultMaxQuota + 1)
  == .error (.proxy "Invalid: quota")

-- the sender registers its operation, with the signed TX encrypted for the recipient...
def prepA : AckPrepare :=
  { transferData := [(tidA, AckTransferData.make bob alice.pk ch tx)], expiresAt := opExp
    signedTxHash := txHash, senderPk := bob.pk }
def s2 : Server := ok! (s1.ackPrepare prepA)
#guard s2.ackPrepare prepA == .ok s2
#guard s2.ackPrepare { prepA with expiresAt := opExp + 1 }
  == .error (.proxyCannotChange "Cannot change: expires_at")
-- ...then posts the consignment encrypted for it
def postA : ConsignmentPost :=
  ConsignmentPost.make bob iidA endpoint ch false (Blob.encrypt cP key) t0
#guard postA.transferId == tidA
#guard s0.consignmentPost postA == .error .invoiceNotReserved
def s3 : Server := ok! (s2.consignmentPost postA)
#guard s3.invoiceCheck [iidA] == [(iidA, .full)]
-- posting it again changes nothing; other bytes cannot replace it
#guard s3.consignmentPost postA == .ok s3
#guard s3.consignmentPost (ConsignmentPost.make bob iidA endpoint ch false (Blob.plain cP) t0)
  == .error (.proxyCannotChange "Cannot change: file")
-- the post must be signed by the key it names
#guard s1.consignmentPost { postA with signature := signMessage carol "x" }
  == .error .invalidContentSignature

-- the recipient lists the invoice's transfers and downloads the consignment
#guard s3.transferList iidA == .ok [(tidA, .pending)]
def got : ConsignmentGetResult := ok! (s3.consignmentGet tidA)
#guard postedBySender iidA tidA got
#guard got.consignmentHash == ch && !got.batch && got.senderTransportEndpoint == endpoint
#guard got.consignment.decryptWith .required (deriveShared alice got.senderPk).symKey
    got.consignmentHash == .ok cP

-- the recipient ACKs: its operation has no other recipient, so the answer releases the TX
def acked : Server × PostAckResponse := ok! (s3.ackPost tidA true (ackSignature alice tidA true ch))
def s4 : Server := acked.1
#guard acked.2.result && acked.2.senderPk == some bob.pk && acked.2.signedTxHash == some txHash
#guard acked.2.expiresAt == some (toString opExp)
#guard acked.2.expiresAt.bind parseI64? == some opExp
#guard (acked.2.signedTx.map fun b =>
    b.decryptWith .required (deriveShared alice bob.pk).symKey txHash)
  == some (.ok txP)
-- ACKing again gets the TX again; the answer cannot change
#guard (s4.ackPost tidA true (ackSignature alice tidA true ch)).map (·.2) == .ok acked.2
#guard (s4.ackPost tidA false (ackSignature alice tidA false ch)).map (·.2)
  == .error (.proxyCannotChange "Cannot change: ack")
-- an ACK the recipient did not sign is refused
#guard (s3.ackPost tidA true (ackSignature carol tidA true ch)).map (·.2)
  == .error .invalidContentSignature
#guard (s3.ackPost tidA true (ackSignature alice tidA true txHash)).map (·.2)
  == .error .invalidContentSignature
-- the sender reads the ACK and checks its signature
def acks : AckGetResult := ok! (s4.ackGet [tidA])
#guard acks.acks == [(tidA, true)]
#guard acks.signatures.all fun (tid, sig) => verifyMessage alice.pk (Msg.ack tid true ch) sig
#guard (s3.ackGet [tidA]).map (·.acks) == .ok []
-- the released TX can no longer be revoked
#guard s4.ackClean [tidA] == .error .proxyTxAlreadyReleased
#guard cleanAckOutcome (errorOf? (s4.ackClean [tidA])) == .ok .released

-- the recipient lets the proxy delete the data; the transfer keeps its quota slot
def s5 : Server := ok! (s4.transferRetrieved tidA)
#guard s5.transferList iidA == .ok [(tidA, .retrieved)]
#guard s5.consignmentGet tidA == .error .noConsignment
#guard s5.invoiceCheck [iidA] == [(iidA, .full)]

/-! ## Retention grace -/

-- past the expiration an ACKed recipient still gets the released TX...
#guard ((s4.tick (opExp - t0 + 60)).ackPost tidA true (ackSignature alice tidA true ch)).map
    (·.2.signedTx.isSome) == .ok true
-- ...until the retention grace has passed: then the proxy forgets the operation
#guard ((s4.tick (opExp - t0 + 86400 + 1)).ackPost tidA true (ackSignature alice tidA true ch)).map
    (·.2) == .error .operationNotFound
#guard senderProxyKnowsOperation (errorOf? ((s4.tick (opExp - t0 + 86400 + 1)).ackGet [tidA]))
  == .ok false
-- an expired operation is still known: registering it again is refused as expired
def s2late : Server := s2.tick (opExp - t0 + 1)
#guard s2late.ackPrepare prepA == .error .expirationInvalid
#guard senderProxyKnowsOperation (errorOf? (s2late.ackGet [tidA])) == .ok true
#guard senderProxyKnowsOperation (errorOf? (s1.ackGet [tidA])) == .ok false
-- operation expirations in the past or too far ahead are refused
#guard s1.ackPrepare { prepA with expiresAt := t0 - 1 } == .error .expirationInvalid
#guard s1.ackPrepare { prepA with expiresAt := t0 + defaultMaxExpirySecs + 1 }
  == .error .expirationInvalid
#guard s1.ackPrepare { prepA with transferData := [] } == .error (.proxy "Missing: transfer_data")
-- a transfer id another operation registered is in use
#guard s2.ackPrepare { prepA with senderPk := carol.pk } == .error .transferIdInUse

/-! ## A batch released on its last ACK -/

def ridD : String := "bcrt:utxob:dave-seal"
def iidD : String := invoiceId ridD dave.pk
def opB : SecretKey := ⟨"bob-batch"⟩
def tidBA : String := transferId iidA opB.pk
def tidBD : String := transferId iidD opB.pk

def b0 : Server := ok! ((ok! (s0.invoicePrepare iidA invoiceExp alice.pk 1)).invoicePrepare
  iidD invoiceExp dave.pk 1)
def prepB : AckPrepare :=
  { transferData := [(tidBA, AckTransferData.make opB alice.pk ch tx),
      (tidBD, AckTransferData.make opB dave.pk ch tx)]
    expiresAt := opExp, signedTxHash := txHash, senderPk := opB.pk }
/-- The batch's post to a recipient. -/
def postB (iid : String) (recipient : SecretKey) : ConsignmentPost :=
  ConsignmentPost.make opB iid endpoint ch true
    (Blob.encrypt cP (deriveShared opB recipient.pk).symKey) t0
def b1 : Server :=
  ok! ((ok! ((ok! (b0.ackPrepare prepB)).consignmentPost (postB iidA alice))).consignmentPost
    (postB iidD dave))
#guard b1.invoiceCheck [iidA, iidD] == [(iidA, .full), (iidD, .full)]
#guard (b1.consignmentGet tidBD).map (·.batch) == .ok true

-- alice ACKs first: nothing is released yet
def bA : Server × PostAckResponse := ok! (b1.ackPost tidBA true (ackSignature alice tidBA true ch))
#guard bA.2 == { result := true, expiresAt := some (toString opExp) }
#guard (bA.1.ackGet [tidBD, tidBA]).map (·.acks) == .ok [(tidBA, true)]
-- dave's ACK completes the operation: his answer carries the TX, encrypted for him
def bD : Server × PostAckResponse := ok! (bA.1.ackPost tidBD true (ackSignature dave tidBD true ch))
#guard (bD.2.signedTx.map fun b => b.decryptWith .required (deriveShared dave opB.pk).symKey txHash)
  == some (.ok txP)
#guard (bD.2.signedTx.map fun b =>
    b.decryptWith .required (deriveShared alice opB.pk).symKey txHash)
  == some (.error (.invalidEncryptedBlob "authentication failed"))
-- alice gets it on her next ACK
#guard (bD.1.ackPost tidBA true (ackSignature alice tidBA true ch)).map (·.2.signedTx.isSome)
  == .ok true
#guard (bD.1.ackGet [tidBA, tidBD]).map (·.acks) == .ok ([(tidBA, true), (tidBD, true)].mergeSort
  fun a b => compare a.1 b.1 != .gt)

/-! ## A NACK -/

def nA : Server × PostAckResponse :=
  ok! (b1.ackPost tidBA false (ackSignature alice tidBA false ch))
#guard (nA.1.ackGet [tidBA, tidBD]).map (·.acks) == .ok [(tidBA, false)]
-- the NACK cannot become an ACK
#guard (nA.1.ackPost tidBA true (ackSignature alice tidBA true ch)).map (·.2)
  == .error (.proxyCannotChange "Cannot change: ack")
-- the other recipient's ACK releases nothing
def nD : Server × PostAckResponse := ok! (nA.1.ackPost tidBD true (ackSignature dave tidBD true ch))
#guard nD.2.signedTx == none
-- the sender can revoke the TX
#guard cleanAckOutcome (errorOf? (nD.1.ackClean [tidBA, tidBD])) == .ok .revoked
-- past the expiration the proxy refuses the ACK: the TX will never be released
#guard ((nD.1.tick (opExp - t0 + 1)).ackPost tidBD true (ackSignature dave tidBD true ch)).map
    (·.2) == .error .operationExpired

/-! ## A revoked operation -/

-- the sender revokes before any ACK
def c1 : Server := ok! (s3.ackClean [tidA])
#guard cleanAckOutcome (errorOf? (s3.ackClean [tidA])) == .ok .revoked
-- registering the operation again reports only the cleared TX, which stays cleared
#guard c1.ackPrepare prepA == .error .signedTxCleared
#guard c1.ackPrepare { prepA with expiresAt := opExp + 1 }
  == .error (.proxyCannotChange "Cannot change: expires_at, signed_tx")
-- the recipient's ACK gets no TX back
def cA : Server × PostAckResponse := ok! (c1.ackPost tidA true (ackSignature alice tidA true ch))
#guard cA.2 == { result := true, expiresAt := some (toString opExp) }
-- past the expiration the proxy refuses the ACK
#guard ((cA.1.tick (opExp - t0 + 1)).ackPost tidA true (ackSignature alice tidA true ch)).map
    (·.2) == .error .operationExpired

/-! ## Transfers without an operation -/

-- a donation or a mint posts its consignment but registers no operation: an ACK finds none
def dn : Server := ok! (s1.consignmentPost postA)
#guard (dn.ackPost tidA true (ackSignature alice tidA true ch)).map (·.2)
  == .error .operationNotFound
#guard (dn.ackPost tidA false (ackSignature alice tidA false ch)).map (·.2)
  == .error .operationNotFound
#guard dn.ackClean [tidA] == .error .operationNotFound
#guard dn.ackGet [tidA] == .error .operationNotFound
-- naming a transfer outside the operation finds none either
#guard s3.ackGet [tidA, rep '0' 64] == .error .operationNotFound

/-! ## Quota, deletion and transfers not posted by their sender -/

def postC : ConsignmentPost := ConsignmentPost.make carol iidA endpoint ch false (Blob.plain cP) t0
-- the quota is taken
#guard s3.consignmentPost postC == .error .invoiceQuotaExceeded
-- deleting the transfer frees its slot, and its id cannot be posted again
def d1 : Server := ok! (s3.transferDelete tidA)
#guard d1.invoiceCheck [iidA] == [(iidA, .available)]
#guard d1.consignmentGet tidA == .error .noConsignment
#guard d1.consignmentPost postA == .error .transferIdDeleted
#guard d1.transferDelete tidA == .ok d1
#guard (d1.consignmentPost postC) matches .ok _
-- the proxy takes a post under a transfer id its key does not derive; the recipient spots it
def forged : ConsignmentPost := { postC with
  transferId := tidA, signature := signMessage carol (Msg.postConsignment tidA ch postC.file.hash) }
def f1 : Server := ok! (s1.consignmentPost forged)
#guard (f1.consignmentGet tidA).map (postedBySender iidA tidA) == .ok false
-- and the sender's own post under that id is refused
#guard f1.consignmentPost postA == .error (.proxyCannotChange "Cannot change: sender_pk, file")

/-! ## An expired invoice -/

def e1 : Server := s1.tick (invoiceExp - t0 + 1)
#guard e1.consignmentPost (ConsignmentPost.make bob iidA endpoint ch false (Blob.plain cP) e1.now)
  == .error .invoiceExpired
-- once the retention grace has passed too, the proxy no longer knows the invoice
def e2 : Server := s1.tick (invoiceExp - t0 + 86400 + 1)
#guard e2.invoiceCheck [iidA] == [(iidA, .unknown)]
#guard e2.transferList iidA == .error .invoiceNotReserved
#guard e2.consignmentPost (ConsignmentPost.make bob iidA endpoint ch false (Blob.plain cP) e2.now)
  == .error .invoiceNotReserved
-- its transfers go with it
#guard (s5.tick (invoiceExp - t0 + 86400 + 1)).consignmentGet tidA == .error .noConsignment

/-! ## Proof of work -/

def sPow : Server := s1.configure fun c => { c with powDifficulty := 6 }
#guard sPow.info.maxPowDifficulty == some "6"
#guard sPow.invoiceCheckFull [iidA] == [(iidA, ⟨.available, "6"⟩)]
-- a post without proof of work is refused with the difficulty it needs
#guard Wire.consignmentPost sPow postA == .error (Err.invalidPow 6)
#guard (errorOf? (Wire.consignmentPost sPow postA)).bind powDifficultyRequired == some 6
#guard sPow.consignmentPost postA == .error (.proxy "Invalid proof of work")
-- the sender retries with that difficulty
#guard (sPow.postConsignmentWithPow postA) matches .ok _
-- more than the wallet computes is not attempted
def sHard : Server := s1.configure fun c => { c with powDifficulty := maxPowDifficulty + 1 }
#guard sHard.postConsignmentWithPow postA == .error (.proxy "Invalid proof of work")
-- the proof of work is for the proxy's time
#guard s1.consignmentPost { postA with powTimestamp := t0 - 301 }
  == .error (.proxy "Invalid: pow_timestamp")

/-! ## Media -/

def media : Payload := .bytes "token image"
def mid : String := keysAB.mediaId media.hash
def mPost : MediaPost := MediaPost.make bob tidA mid (Blob.encrypt media key)
def m1 : Server := ok! (s3.mediaPost mPost)
#guard (m1.mediaGet tidA mid).map (·.decryptWith .required (deriveShared alice bob.pk).symKey
    media.hash) == .ok (.ok media)
#guard m1.mediaPost mPost == .ok m1
#guard m1.mediaGet tidA (rep '0' 64) == .error .noMedia
-- only the transfer's sender posts its media
#guard s3.mediaPost (MediaPost.make carol tidA mid (Blob.plain media))
  == .error .invalidContentSignature
-- the media limit
def m1one : Server := m1.configure fun c => { c with maxMedia := 1 }
#guard proxyMaxMedia m1one.info == some 1
#guard m1one.mediaPost (MediaPost.make bob tidA (rep '1' 64) (Blob.plain media))
  == .error .proxyTooManyMedia
-- retrieved data takes its media with it
#guard (ok! (m1.transferRetrieved tidA)).mediaGet tidA mid == .error .noMedia

/-! ## A draining proxy -/

def sDrain : Server := s2.configure fun c => { c with draining := true }
#guard sDrain.invoicePrepare iidD invoiceExp dave.pk 1 == .error .proxyDraining
#guard sDrain.consignmentPost postA == .error .proxyDraining
#guard sDrain.ackPrepare prepB == .error .proxyDraining
-- calls on started transfers still work
#guard (sDrain.ackPost tidA true (ackSignature alice tidA true ch)) matches .ok _
#guard sDrain.invoiceCheck [iidA] == [(iidA, .available)]

/-! ## Authenticated calls -/

def authKey : SecretKey := ⟨"proxy-auth"⟩
def sAuth : Server := s0.configure fun c => { c with authPk := some authKey.pk }
def invoiceAuth (k : SecretKey) : Ed25519Sig :=
  signMessage k (Msg.prepareInvoiceAuth iidA (toString invoiceExp) alice.pk 1)
-- a proxy with authentication refuses an unsigned reservation, or one signed by another key
#guard sAuth.invoicePrepare iidA invoiceExp alice.pk 1 == .error (.proxy "Missing: signature")
#guard sAuth.invoicePrepare iidA invoiceExp alice.pk 1 (some (invoiceAuth carol))
  == .error .invalidProxyAuthSignature
def sAuth1 : Server :=
  ok! (sAuth.invoicePrepare iidA invoiceExp alice.pk 1 (some (invoiceAuth authKey)))
#guard sAuth1.invoiceCheck [iidA] == [(iidA, .available)]
-- and the same for `ack.prepare`
#guard sAuth1.ackPrepare prepA == .error (.proxy "Missing: signature")
#guard (sAuth1.ackPrepare { prepA with signature := some (signMessage authKey
    (Msg.prepareAckAuth bob.pk (toString opExp) txHash prepA.transferData)) }) matches .ok _
-- `ack.get` and `ack.clean` are signed by the sender over its transfer ids
#guard s4.ackGetAuth [tidA] (signMessage bob (Msg.getAck [tidA] (toString t0))) t0
  == s4.ackGet [tidA]
#guard s4.ackGetAuth [tidA] (signMessage alice (Msg.getAck [tidA] (toString t0))) t0
  == .error .invalidEndpointAuthSignature
#guard s4.ackGetAuth [tidA] (signMessage bob (Msg.getAck [tidA] (toString (t0 - 301)))) (t0 - 301)
  == .error (.proxy "Invalid: timestamp")
#guard s3.ackCleanAuth [tidA] (signMessage bob (Msg.cleanAck [tidA])) == s3.ackClean [tidA]
#guard s3.ackCleanAuth [tidA] (signMessage carol (Msg.cleanAck [tidA]))
  == .error .invalidEndpointAuthSignature
-- the recipient calls are signed by the invoice's key
#guard s3.transferListAuth iidA (signMessage alice (Msg.listTransfers iidA (toString t0))) t0
  == .ok [(tidA, .pending)]
#guard s3.transferListAuth iidA (signMessage bob (Msg.listTransfers iidA (toString t0))) t0
  == .error .invalidEndpointAuthSignature
#guard s3.transferRetrievedAuth tidA (signMessage alice (Msg.transferRetrieved tidA))
  == s3.transferRetrieved tidA
#guard s3.transferRetrievedAuth tidA (signMessage bob (Msg.transferRetrieved tidA))
  == .error .invalidEndpointAuthSignature
#guard s3.transferDeleteAuth tidA (signMessage alice (Msg.deleteTransfer tidA))
  == s3.transferDelete tidA
#guard s3.transferDeleteAuth tidA (signMessage carol (Msg.deleteTransfer tidA))
  == .error .invalidEndpointAuthSignature

/-! ## The proxies of an invoice -/

def drainingProxy : Server :=
  (Server.init "http://draining.test" t0).configure fun c => { c with draining := true }
def oldProxy : Server := { s0 with info := { s0.info with protocolVersion := "0.2" } }
def reserveA (proxies : List Server) (keys : List (String × SecretKey) := []) :
    Except Error Nat :=
  (reserveInvoice proxies iidA invoiceExp alice.pk 1 keys).map (·.2)

-- a draining proxy is skipped; the deadline is the expiration plus the longest grace
#guard reserveA [drainingProxy, s0] == .ok (invoiceExp + 86400)
#guard reserveA [Server.init "http://short.test" t0 3600, s0] == .ok (invoiceExp + 86400)
#guard ((reserveInvoice [drainingProxy, s0] iidA invoiceExp alice.pk 1).map
    fun r => r.1.map (·.invoiceCheck [iidA])) == .ok [[(iidA, .unknown)], [(iidA, .available)]]
-- with no reservation: draining if a proxy was, else no valid endpoint
#guard reserveA [drainingProxy] == .error .proxyDraining
#guard reserveA [oldProxy] == .error .noValidTransportEndpoint
#guard reserveA [] == .error .noValidTransportEndpoint
-- any other refusal ends the receive
#guard (reserveInvoice [s0] iidA (t0 - 1) alice.pk 1).map (·.2) == .error .expirationInvalid
#guard reserveA [sAuth] == .error (.proxy "Missing: signature")
-- a proxy with authentication gets the signature of its key
#guard reserveA [sAuth] [(sAuth.url, authKey)] == .ok (invoiceExp + 86400)
-- a send needs one proxy where the invoice is available
#guard checkInvoiceAvailable [s0, s1] iidA == .ok ()
#guard checkInvoiceAvailable [s3, s0] iidA == .error .invoiceQuotaExceeded
#guard checkInvoiceAvailable [s0] iidA == .error .invoiceNotReserved
#guard checkInvoiceAvailable [] iidA == .error .noValidTransportEndpoint
-- what a sender uploads for each kind of recipient
#guard Blob.forRecipient .unsupported key cP == .plain cP
#guard Blob.forRecipient .optional key cP == Blob.encrypt cP key
#guard (got.consignment.decryptWith .required key ch).map (·.consignment?) == .ok (some consignment)

end Rgb.Examples.Proxy
