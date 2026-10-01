# Reproducing the `sum_of_slice` benchmark

This takes one real Rust function, dalek-lite's
[`Scalar::sum_of_slice`](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/de9ebf01599fedbbced28b938e2c36c538fe4ae5/curve25519-dalek/src/scalar_helpers.rs#L158-L234),
from its Verus-verified source to a proof checked by the Lean kernel.

You need `rustup`, `elan`, `python3`, and `cvc5` on your `PATH`.

## 1. Clone

Run this in a new, empty directory. The four repositories must sit side by side under
these names.

```
mkdir dalek-demo && cd dalek-demo

git clone --branch boogie               https://github.com/ccodel/verus.git
git clone --branch lean-export-path-fix https://github.com/kondylidou/dalek-lite.git
git clone --branch boole                https://github.com/kondylidou/verus-boole.git
git clone --branch keynote-integration  https://github.com/strata-org/Strata-Boole.git
```

## 2. Build

```
cd verus/source
./tools/get-z3.sh
source ../tools/activate
vargo build --release --features lean
cd ../..

cd Strata-Boole
lake exe cache get
lake build StrataBoole smt
cd ..

cd verus-boole
lake build
cd ..
```

## 3. Run

```
cd verus-boole
sh dalek/rust_to_boole.sh dalek/input/scalar_helpers.rs --only sum_of_slice \
    --dalek-lite ../dalek-lite \
    --strata-boole ../Strata-Boole \
    --verus-bin ../verus/source/target-verus/release
```

It should end with:

```
cvc5: 36/36 obligations pass
Lean: StrataBooleTest.dalek_sum_of_slice builds: every obligation checked by the Lean kernel
```

Building and the first run take about 30 minutes in total. After that, a run takes
under two minutes.

## What you get

The run writes `Strata-Boole/StrataBooleTest/dalek_sum_of_slice.lean`, which has three
parts:

1. The Rust source, as a comment.
2. Its translation to Boole, with all 36 proof obligations checked by the cvc5 solver.
3. The same 36 obligations proved again inside Lean, so the solver no longer has to be
   trusted.

The translation keeps the Rust types (`u8` as an 8-bit value, `nat` as a natural number)
and the contract of `sum_of_slice` has the same clauses as in the source. The file is
already in the repository; the run regenerates it identically.

## If something fails

The logs are in `verus-boole/dalek/`:

- `export_json/export.log` for the Verus step,
- `out/sum_of_slice.cvc5.log` for cvc5,
- `out/sum_of_slice.lean.log` for Lean.
