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

### `import StrataBoole.Nat`

- **Binary nat library**: `Strata.BooleNat.natLibrary`, `Strata.BooleNat.prepend`

### `import StrataBoole.MetaVerifier`

The `gen_smt_vcs_boole` tactic and `Strata.smtVCsCorrectBoole` are available
by importing `StrataBoole.MetaVerifier` directly.
-/
