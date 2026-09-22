/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole
public import StrataBoole.Verify

/-! ## Strata Boole Public Interface

Parsing, translation to Core, verification, and pretty-printing for the Boole
dialect of Strata.

### `import StrataBoole`

- **Types**: `Strata.Boole.Type`, `Strata.Boole.Expr`, `Strata.Boole.Program`
- **Parsing**: `Strata.Boole.getProgram`
- **Translation**: `Strata.Boole.toCoreProgram`
- **Type checking**: `Strata.Boole.typeCheck`
- **Verification**: `Strata.Boole.verify`
- **VC generation**: `Strata.Boole.genVCs`
- **Pretty-printing**: `Strata.Boole.formatProgram`

### `import StrataBoole.Nat` (specification only)

- **Binary nat library, as a readable Core-syntax spec**: `Strata.BooleNat.natLibrary`,
  `Strata.BooleNat.prepend`.  Not part of the implementation: `Strata.Boole.verify`
  injects its own copy (`natCorePreamble` in `StrataBoole/Verify.lean`) whenever a
  program uses `nat`/`pos`, and nothing imports this module.  Build it with
  `lake build StrataBoole.Nat` to check the spec still parses.

### `import StrataBoole.MetaVerifier`

The `gen_smt_vcs_boole` tactic and `Strata.smtVCsCorrectBoole` are available
by importing `StrataBoole.MetaVerifier` directly.
-/
