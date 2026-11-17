/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

/-!
# Unsupported global types must fail lowering

Boole encodes each top-level `var` as an implicit parameter of every
procedure. The only place that registers those globals is the pre-pass in
`toCoreProgram`: it lowers the declared type with `toCoreMonoType` and inserts
the name into `globalVarTypes`.

The old pre-pass discarded a type-lowering error and continued. An unused
`var g : real` therefore produced a Core program whose procedures had no `g`
parameter — the same Core shape as a program that never declared `g`. The
pre-pass now propagates that error, so lowering fails at the declaration.

The empty procedure is intentional. The body never mentions `g`, so no later
check can mask a silent drop; the only evidence of retention is the Core
parameter list.
-/

namespace Strata

/-- Parse and lower a Boole program; surface the diagnostic as a string. -/
private def lower (p : StrataDDM.Program) : Except String Core.Program := do
  let prog ← (Boole.getProgram p).mapError toString
  (Boole.toCoreProgram prog p.globalContext).mapError fun e =>
    toString (e.format none)

/-! ## Rejection: a global whose type Core cannot lower -/

-- `g` is unused. Before the fix, lowering succeeded and `noop` had no inputs.
private def unusedRealGlobal :=
#strata
program Boole;
var g : real;
procedure noop() returns () {};
#end

-- Keep only the stable part of the diagnostic: source ranges shift with edits.
/-- info: Except.error "Unsupported Boole type" -/
#guard_msgs in
#eval show Except String Unit from
  match lower unusedRealGlobal with
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
