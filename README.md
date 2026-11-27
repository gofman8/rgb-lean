# rgb-lean

A Lean 4 model of the RGB protocol and of the [rgb-lib] wallet library: what
RGB can do, the rules it enforces, the bounds of every value and the expected
behaviour of each operation.

The model follows rgb-lib `0.3.0-beta.7` and the RGB crates it uses
(`rgb-consensus`, `rgb-ops`, `rgb-schemas`, `rgb-invoicing`, `rgb-psbt-utils`,
all `0.11.2-rc.2`).

It does not prove that RGB is secure. It assumes the cryptography works and
states, as executable Lean, what the protocol and the library do:

- **data**: every type that RGB commits to or rgb-lib stores, with its bounds;
- **rules**: every check, as a function that returns the error the library
  returns;
- **behaviour**: operations as state machines over a wallet, a stash and a
  simulated Bitcoin chain;
- **examples**: scenarios that run at build time (`#guard`), such as issuing an
  asset, sending it, refreshing both wallets and settling.

## Build

```sh
./scripts/check.sh   # or: lake build
```

The build runs every scenario check. Lean `4.36.0`, core library only.

## How the model treats cryptography

RGB names objects by tagged hashes. The model keeps the tag and a canonical
encoding of the committed data in place of the hash (`Rgb.Core.Digest`), so two
ids are equal exactly when the committed data is equal: a collision-resistant
hash by construction, with no axiom. Signatures and key derivation are
represented by the data they bind. Hiding (a concealed seal does not reveal its
outpoint) is assumed and not modelled.

[rgb-lib]: https://github.com/RGB-Tools/rgb-lib
