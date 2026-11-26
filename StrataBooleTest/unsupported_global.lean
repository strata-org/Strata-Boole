/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
# Unsupported global types must fail lowering

Boole encodes each top-level variable as an implicit procedure parameter.
Failure to lower its type must be propagated, rather than silently omitting
the variable from the Core program.

`bv bool` deliberately supplies a value type where a bitvector width is
required. It remains invalid independently of support for real, Set or regex.
The empty procedure ensures no later use of the global can mask its omission.
-/

namespace Strata

/-- Parse and lower a Boole program; surface the diagnostic as a string. -/
private def lower (p : StrataDDM.Program) : Except String Core.Program := do
  let prog ← (Boole.getProgram p).mapError toString
  (Boole.toCoreProgram prog p.globalContext).mapError fun e =>
    toString (e.format none)

/-! ## Rejection: an invalid bitvector width on an unused global -/

-- The type-lowering error must be reported even though g is unused.
private def invalidGlobalVariable :=
#strata
program Boole;
var g : bv bool;
procedure noop() returns () {};
#end

-- Keep only the stable part of the diagnostic: source ranges shift with edits.
/-- info: Except.error "Unsupported Boole type" -/
#guard_msgs in
#eval show Except String Unit from
  match lower invalidGlobalVariable with
  | .error e =>
    if (e.splitOn "Unsupported Boole type").length > 1 then
      .error "Unsupported Boole type"
    else
      .error e
  | .ok _ => .ok ()

/-! ## Retention: the same shape with a supported type -/

-- Same unused global and empty procedure. `int` lowers, so `g` is registered
-- and appears as a read-only input of every procedure — including this one.
private def unusedIntGlobal :=
#strata
program Boole;
var g : int;
procedure noop() returns () {};
#end

/-- info: Except.ok ["g"] -/
#guard_msgs in
#eval show Except String (List String) from do
  let cp ← lower unusedIntGlobal
  let some proc := cp.findProcByString? "noop" | .error "missing noop"
  return proc.header.inputs.toList.map fun (id, _) => id.name

end Strata
