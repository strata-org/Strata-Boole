# Reproducing the `sum_of_slice` benchmark

This regenerates `StrataBooleTest/dalek_sum_of_slice.lean` from Rust source: a real
dalek-lite function
([`Scalar::sum_of_slice`](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/de9ebf01599fedbbced28b938e2c36c538fe4ae5/curve25519-dalek/src/scalar_helpers.rs#L158-L234)),
verified by Verus, translated to Boole, checked by cvc5, and then checked again by the
Lean kernel.

The generated file has three levels:

1. **Rust.** The Verus-annotated function, kept as a comment.
2. **Boole + cvc5.** The translated Boole program under `#eval Strata.Boole.verify "cvc5"`,
   with the result of all 36 obligations pinned by `#guard_msgs`. Here cvc5 is trusted.
3. **Lean kernel.** `gen_smt_vcs_boole` turns the same 36 obligations into Lean goals.
   The 28 that belong to the program are closed by `inline_boole_defs; smt`: cvc5 proves
   the goal and lean-smt replays that proof in the Lean kernel, so the solver is no
   longer trusted. The other 8 belong to Boole's `nat` library and are proved by hand,
   as are the small bitvector side goals that lean-smt leaves behind.

The translation stays close to the source. `u8` is `bv8`, Verus `nat` is Boole's native
`nat`, and the contract of `sum_of_slice` has the same clauses as in Rust.

## Requirements

`rustup`, `elan`, `python3`, and a `cvc5` executable on `PATH`. Level 2 calls that
executable; Level 3 uses the copy bundled with lean-smt.

## 1. Clone four repositories as siblings

```
mkdir workspace && cd workspace

git clone --branch boogie               https://github.com/ccodel/verus.git
git clone --branch lean-export-path-fix https://github.com/kondylidou/dalek-lite.git
git clone --branch boole                https://github.com/kondylidou/verus-boole.git
git clone --branch keynote-integration  https://github.com/strata-org/Strata-Boole.git
```

The directory names matter. dalek-lite finds the Verus fork at `../verus`, and the
translator finds Strata-Boole at `../Strata-Boole`.

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

`lake exe cache get` downloads prebuilt mathlib, which lean-smt depends on. Without it
the `smt` target compiles mathlib from source.

The first build is slow. Strata is compiled twice, once for Strata-Boole and once for
the translator, because each keeps its own copy of its dependencies.

## 3. Run

```
cd verus-boole
sh dalek/rust_to_boole.sh dalek/input/scalar_helpers.rs --only sum_of_slice \
    --dalek-lite ../dalek-lite \
    --strata-boole ../Strata-Boole \
    --verus-bin ../verus/source/target-verus/release
```

Expected output:

```
exported: curve25519_dalek_scalar.json curve25519_dalek_scalar_helpers.json ...
wrote .../verus-boole/dalek/out/sum_of_slice.boole.st (83 lines)
cvc5: 36/36 obligations pass
wrote .../Strata-Boole/StrataBooleTest/dalek_sum_of_slice.lean
Lean: StrataBooleTest.dalek_sum_of_slice builds: every obligation checked by the Lean kernel
```

The first run is much slower than later ones, since Verus has to build vstd and the
dalek-lite crate. With warm caches a run takes between one and two minutes, of which
the Lean stage is about half a minute.

The script overwrites `StrataBooleTest/dalek_sum_of_slice.lean`. On an unchanged
checkout the result is identical to the committed file, so `git status` in Strata-Boole
stays clean.

## What the script does

1. Copies the Rust module into the dalek-lite crate and has the Verus fork verify it and
   export its intermediate representation as JSON.
2. Runs the translator (`verus-lean boole --only sum_of_slice ...`) to produce one Boole
   program, `dalek/out/sum_of_slice.boole.st`.
3. Builds a throwaway copy with Level 2 only, to record cvc5's verdict on each obligation.
4. Writes the final file with that record pinned and Level 3 on top, and builds it.

## Options

`--lean-only` skips Level 2 and goes straight to Level 3. It is faster, but if Level 3
then fails you cannot tell whether cvc5 could not prove the obligation or proved it and
the replay in Lean failed. Level 2 is what separates those two cases.

`--no-lean` stops after step 2 and only writes the Boole program.

## If something fails

- `the Verus export produced no JSON`: see `verus-boole/dalek/export_json/export.log`.
  The usual cause is that `verus` and `dalek-lite` are not siblings.
- `cvc5: N/36 obligations pass  <-- NOT ALL PASS`: see
  `verus-boole/dalek/out/sum_of_slice.cvc5.log`.
- `Lean: ... FAILED`: see `verus-boole/dalek/out/sum_of_slice.lean.log`.
