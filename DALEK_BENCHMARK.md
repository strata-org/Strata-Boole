# Reproducing the `sum_of_slice` benchmark

Produces `StrataBooleTest/dalek_sum_of_slice_translated.lean`: a real dalek-lite function
([`scalar_helpers.rs#L158-L234`](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/de9ebf01599fedbbced28b938e2c36c538fe4ae5/curve25519-dalek/src/scalar_helpers.rs#L158-L234),
`Scalar::sum_of_slice`), translated to Boole and certified by lean-smt.

Three levels in the output file: **Level 1** is the original Rust, kept as a comment.
**Level 2** is the Boole program plus `#eval Strata.Boole.verify "cvc5"` — cvc5 trusted
directly. **Level 3** is `gen_smt_vcs_boole; smt` — cvc5's proof reconstructed and checked
by Lean's own kernel.

## 1. Clone four repos as siblings

```
mkdir workspace && cd workspace

git clone --branch boogie https://github.com/ccodel/verus.git

git clone --branch lean-export-path-fix git@github.com:kondylidou/dalek-lite.git

git clone --branch boole git@github.com:kondylidou/verus-boogie.git

git clone --branch lean_smt git@github.com:strata-org/Strata-Boole.git
```

## 2. Build

```
cd verus/source
./tools/get-z3.sh
source ../tools/activate
vargo build --release --features lean
cd ../..

cd verus-boogie && lake build && cd ..

cd Strata-Boole && lake build StrataBoole && cd ..
```

## 3. Run

```
cd verus-boogie
sh dalek/rust_to_boole.sh dalek/input/scalar_helpers.rs --only sum_of_slice \
    --dalek-lite ../dalek-lite \
    --strata-boole ../Strata-Boole \
    --verus-bin ../verus/source/target-verus/release
```

Ends with `Lean: ... builds — every obligation certified by lean-smt`. Output:
`Strata-Boole/StrataBooleTest/dalek_sum_of_slice_translated.lean`.

Takes a few minutes (mostly the Verus verification step); the first run also compiles
`vstd` into `dalek-lite`'s target directory, so expect roughly twice that once.

Add `--lean-only` to skip Level 2 entirely and go straight to Level 3 — faster, but if
Level 3 then fails you lose the ability to tell whether cvc5 couldn't prove the obligation
or proved it and Lean's replay choked; Level 2 is what makes that distinction.
