# rgb-lean

A Lean 4 model of the RGB protocol and of the [rgb-lib] wallet library: what
RGB can do, the rules it enforces, the bounds of every value and the expected
behaviour of each operation, written as executable Lean.

The model follows rgb-lib `0.3.0-beta.7` and the RGB crates it uses
(`rgb-consensus`, `rgb-ops`, `rgb-schemas`, `rgb-invoicing`, `rgb-psbt-utils`,
all `0.11.2-rc.2`).

It does not prove that RGB is secure. It assumes the cryptography works and
states what the protocol and the library do:

- **data**: every type that RGB commits to or rgb-lib stores, with its bounds;
- **rules**: every check, as a function that returns the error rgb-lib returns;
- **behaviour**: operations as state machines over wallets, stashes and a
  simulated Bitcoin chain;
- **scenarios**: `#guard` checks that run at build time, from a single seal to
  two wallets issuing, sending, refreshing and settling;
- **theorems**: statements that hold for every input, proven in Lean.

## Build

```sh
./scripts/check.sh   # refuses sorry/axioms, then lake build (runs every scenario)
```

Lean `4.36.0` (see `lean-toolchain`), core library only. CI runs the same script.

## How the model treats cryptography

RGB names objects by tagged hashes. The model keeps the tag and a canonical
encoding of the committed data in place of the hash (`Rgb.Core.Digest`): two
ids are equal exactly when the committed data is equal, which models a
collision-resistant hash without an axiom. A signature records its signing key
and message and verifies for that key's public key. Hiding (a concealed seal
does not reveal its outpoint) is assumed, not modelled. Where RGB reads a hash as
a number (MPC leaf positions), the model reads 64 bits of the digest.

## What is modelled

| Area | Modules | Content |
|---|---|---|
| Core | `Core.Digest`, `Core.Collections` | tagged commitments, ordered maps and sets, confinement bounds |
| Bitcoin | `Bitcoin.Tx`, `Bitcoin.Chain`, `Bitcoin.Merkle` | transactions, outpoints, chain networks; a chain with mempool, blocks, confirmations, reorgs; block merkle trees |
| Seals | `Consensus.Seal` | genesis and graph seals, witness-output seals, concealment, seal closing |
| Operations | `Consensus.Ids`, `Consensus.Operation`, `Consensus.Bundle` | genesis, transitions, assignments, global state, metadata, operation ids, transition bundles |
| Schemas | `Consensus.Schema`, `Consensus.Occurrences`, `Schemas.Numbers`, `Schemas.Standard` | schema structure, occurrences; NIA, CFA, UDA, IFA, BFA and PFA with their AluVM scripts written out instruction by instruction |
| VM | `Consensus.Vm` | an interpreter of the RGB opcodes (`svs`, `sas`, `sps`, `ldg`, `ldc`, `ldm`, `vts`, `plc`, ...) and the AluVM base instructions the scripts use; error codes from `a8[0]`; bridge lock claims |
| Commitments | `Commit.Mpc`, `Commit.Dbc` | multi-protocol commitment trees and proofs; opret and tapret commitments; anchors; SPV proofs |
| Validation | `Consensus.Validation`, `Consensus.Resolver` | both validation phases with every failure and warning; witness resolvers |
| Standard types | `Stl.Types`, `Stl.Value` | ticker, name, details, precision, terms, token data, EVM and bridge types, with their bounds |
| Containers and stash | `Ops.State`, `Ops.Consignment`, `Ops.Psbt`, `Ops.Witness`, `Ops.Stock` | consignments, fascia; RGB data in a PSBT (transitions, consumer maps, opret host) and its commit; the stash: import, acceptance, composition, visibility, reorg (in)validation |
| Wallet | `Lib.*` | rgb-lib: constants, enums, all 166 errors, objects, database, wallet state, balances, UTXO slots, vanilla operations, issuance of the five schemas, receive, send, refresh, out-of-band exchange, fail and delete, inflate, burn, link, reject lists, the transfer status machine |

## Bounds at a glance

The code holds each bound once; this table only points to them.

| Bound | Value | Where |
|---|---|---|
| inputs of a transition, assignments of a type, bundle input map, known transitions | 1 to 65 535 | `Consensus.Operation`, `Consensus.Bundle` |
| global state types / metadata types of an operation | at most 255 | `Consensus.Operation` |
| values of a global type in one operation | 1 to 65 535 (the schema may allow fewer) | `Consensus.Validation` |
| a structured value, a metadata value | at most 65 535 bytes | `Consensus.Operation` |
| issuer identity | 1 to 4 096 printable ASCII chars | `Consensus.Operation` |
| fungible amounts | `u64`, every output at least 1 | `Consensus.Vm` |
| MPC tree depth / proof path / cofactor attempts | 3 to 31 / at most 31 / 500 | `Commit.Mpc` |
| SPV proof path | at most 32 | `Commit.Dbc` |
| ticker / unicode ticker (BFA) / name / details | 1–8 / 1–8 chars / 1–40 / 1–255 bytes | `Stl.Types` |
| precision / attachments of a token / reject list URL | 0–18 / at most 20 / 1–8 000 | `Stl.Types` |
| allocations per UTXO | `min(max_allocations_per_utxo, 65 535)` | `Lib.Objects` |
| transport endpoints of a receive or recipient | at most 3 | `Lib.Constants` |
| invoice and operation expiration | at most 10 years ahead; an operation at least 300 s ahead and 600 s before the earliest invoice it pays | `Lib.Constants`, `Lib.Send` |
| fee rate | at least 1 sat/vB, `rate × 250` fits `u64` | `Lib.Vanilla` |
| fee estimation target | 1 to 1 008 blocks | `Lib.Contracts` |
| imported contract | at most 16 MiB | `Lib.Constants` |
| reject list | at most 100 000 entries, 7 900 000 bytes | `Lib.RejectList` |
| sender proxy retention grace a receiver accepts | at least one day | `Lib.Constants` |

## Scenarios (`Rgb/Examples`)

- `Chain`: broadcast, double spend, mining, rollback; merkle branches.
- `Operations`: operation ids, concealment, bundles, ordering inside a bundle.
- `Commitments`: MPC trees for five contracts, opret and tapret, SPV proofs.
- `Validation`: an NIA transfer and every way consensus refuses one.
- `Schemas`: IFA inflation, burn and link; UDA fractions; BFA mints and their
  bridge claims; PFA signatures; script offsets as in rgb-schemas.
- `Stock`: stashes through a transfer and a reorganisation.
- `Wallet`, `Transfer`, `Operations2`: two rgb-lib wallets: setup, issuance,
  blind and witness receives, sends, donations, out-of-band exchange, refresh,
  settlement, balances, inflate, burn, link, failing and deleting transfers.
- `SafeHeight`: a payment settled with zero confirmations and forwarded at once;
  the next receiver waits for the history to be mined; listings; the
  consistency check of `go_online`.
- `Contracts`: contract import and export, fee estimation.
- `Psbt`: double spends inside a PSBT, opret host, commit rules.
- `RejectList`: reject-list decisions.

## Theorems (`Rgb/Properties`, `Rgb/Lib/StateMachine`)

- occurrences accept exactly the counts between their bounds;
- revealing or concealing a seal never changes an operation id;
- a witness closes a seal only by spending its outpoint;
- a passing `svs` means inputs and outputs sum to the same amount; `sas`/`sps`
  fix the output/input sums; outputs are never zero;
- the transfer status machine: final statuses have no exit, `initiated` is never
  refreshed, settlement only by refresh from a status that saw the transaction;
- the bundle id depends on the input map only; a passing opret or tapret
  verification puts the commitment in the first `OP_RETURN` or taproot output;
- fee-rate bounds, wallet creation rules, allocation predicates.

## Model simplifications

- Ids, keys and signatures are symbolic (see above); transactions carry no
  witnesses, and signing returns the unsigned transaction.
- Strict types are represented by the standard types themselves; a value
  conforms to a semantic type when it is of that type and within its bounds.
- Fees use a fixed size formula; dust limits are those of the output type.
- A send spends all state of the asset on its selected UTXOs.
- A received witness counts as a donation when it is already on chain.

[rgb-lib]: https://github.com/RGB-Tools/rgb-lib
