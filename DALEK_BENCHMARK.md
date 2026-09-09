# The dalek-lite benchmark pipeline

How `StrataBooleTest/dalek_sum_of_slice_translated.lean` (and any similar file) is produced:
a Verus-annotated Rust function, translated end to end into a three-level Strata-Boole
benchmark (Verus source, Boole program with a cvc5 result, a Lean theorem certified by
lean-smt). The driver script lives in the sibling `verus-boogie` repo, not here.

## Setup (one time)

Four repositories, laid out as siblings under one directory — the paths inside them
(`dalek-lite`'s `Cargo.toml`, `verus-boogie`'s `lakefile.lean`) are relative and expect
exactly this layout:

```
<workspace>/
  verus/            Verus fork with the lean-export feature
  dalek-lite/        the Rust crate a benchmark's function is verified in
  verus-boogie/      the Rust -> Boole translator (this session's fork/branch)
  Strata-Boole/      this repo
```

1. **Verus fork** (provides `--export-lean-all`; not a personal fork — shared upstream):
   ```
   git clone --branch boogie https://github.com/ccodel/verus.git
   cd verus/source
   vargo build --release --features lean
   ```
   Toolchain: rustc 1.93.1 (pinned in the fork's `rust-toolchain.toml`). This produces
   `verus/source/target-verus/release/` (the `--verus-bin` argument below).

2. **dalek-lite** (this session's fork — has the one needed fix already):
   ```
   git clone --branch lean-export-path-fix git@github.com:kondylidou/dalek-lite.git
   ```
   Its `curve25519-dalek/Cargo.toml` points `vstd`/`verus_builtin`/`verus_builtin_macros` at
   `../../verus/source/...` — a relative path assuming the sibling layout above. If your
   layout differs, edit those three lines. (Upstream is
   `Beneficial-AI-Foundation/dalek-lite`, branch `main` — everything else in the crate is
   identical to it.)

3. **verus-boogie** (this session's fork) — clone next to the above; its `lakefile.lean`
   requires `../Strata-Boole`, so it must sit as a sibling of this repo:
   ```
   git clone --branch boole git@github.com:kondylidou/verus-boogie.git
   cd verus-boogie
   lake build
   ```
   Builds `.lake/build/bin/verus-lean`, the translator binary the script calls.

4. **This repo (Strata-Boole)**:
   ```
   git clone --branch lean_smt git@github.com:strata-org/Strata-Boole.git
   cd Strata-Boole
   lake build StrataBoole
   ```
   `lakefile.toml` resolves `Strata` from `https://github.com/kondylidou/Strata`, branch
   `fix/gen-vcs-precond-termcheck` (this session's fork of strata-org/Strata#1471) — fetched
   automatically by `lake build`, already pushed, nothing extra to clone by hand.

## Running the pipeline

From inside `verus-boogie`:

```
sh dalek/rust_to_boole.sh <module.rs> --only <fn> \
    --dalek-lite <path/to/dalek-lite> \
    --strata-boole <path/to/Strata-Boole> \
    --verus-bin <path/to/verus>/source/target-verus/release
```

Example, with the sibling layout above:

```
sh dalek/rust_to_boole.sh dalek/input/scalar_helpers.rs --only sum_of_slice \
    --dalek-lite ../dalek-lite \
    --strata-boole ../Strata-Boole \
    --verus-bin ../verus/source/target-verus/release
```

Writes `verus-boogie/dalek/out/sum_of_slice.boole.st` (the Boole program) and, in this
repo, `StrataBooleTest/dalek_sum_of_slice_translated.lean` (the three-level file, built —
cvc5 result and Lean kernel certification both checked before the script prints success).
See the comment block at the top of `verus-boogie/dalek/rust_to_boole.sh` for what each
translator flag does and for the optional `--lean-out`/`--no-lean` flags.

Takes a few minutes, almost all of it the Verus export step (`cargo verus verify` on the
whole crate) — the translation and the Lean build in this repo are fast.
