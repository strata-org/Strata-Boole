/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
# Real-number lowering regressions

Real declarations and expressions lower to Core's existing real type and
operators. Decimal and fraction literals preserve their exact rational values.

Each named assertion checks one outcome. The examples cover nested types,
arithmetic, comparisons, contracts, collections, calls and global state.
Negative tests check invalid literals, unsupported modulo and a false claim;
integer and bitvector controls check that numeric dispatch remains unchanged.
-/

/-- Lower source code and expose diagnostics without depending on their Lean representation. -/
private def lower (source : StrataDDM.Program) : Except String Core.Program := do
  let program ← (Boole.getProgram source).mapError toString
  (Boole.toCoreProgram program source.globalContext).mapError fun diagnostic =>
    toString (diagnostic.format none)

/-! ## Real types, including nested types and unused globals -/

-- Even an unused global must appear in noop's Core inputs. Nested types
-- exercise both Map arguments and composition of type constructors.
private def realTypePositions :=
#strata
program Boole;

var unused_real : real;

procedure noop() returns () {};

procedure real_type_positions(x: real, s: Sequence real, m: Map int real,
                             f: real -> real, keys: Map real int,
                             nested: Sequence (Map int real)) returns (r: real)
{
  var local: real;
  local := x;
  r := local;
};
#end

#guard match lower realTypePositions with
  | .error _ => false
  | .ok program =>
    match program.findProcByString? "noop" with
    | none => false
    | some procedure =>
      procedure.header.inputs.toList.map (fun (name, ty) => (name.name, ty)) ==
        [("unused_real", Lambda.LMonoTy.real)]

#guard match lower realTypePositions with
  | .error _ => false
  | .ok program =>
    match program.findProcByString? "real_type_positions" with
    | none => false
    | some procedure =>
      procedure.header.inputs.toList.map (·.2) ==
        [.real, .real, .tcons "Sequence" [.real], .tcons "Map" [.int, .real],
         .arrow .real .real, .tcons "Map" [.real, .int],
         .tcons "Sequence" [.tcons "Map" [.int, .real]]] &&
      procedure.header.outputs.toList.map (·.2) == [.real]

/-! ## Decimal and rational literals are exact -/

-- Decimal arithmetic uses exact rationals rather than floating-point
-- approximations; fraction literals also preserve normalization and sign.
private def realLiterals :=
#strata
program Boole;

procedure real_literals() returns ()
{
  assert [decimal_is_exact]: 0.1 + 0.2 == 0.3;
  assert [decimal_matches_fraction]: 1.25 == frac{5, 4};
  assert [nonterminating_fraction]: frac{1, 3} * 3.0 == 1.0;
  assert [fraction_is_normalized]: frac{2, 6} == frac{1, 3};
  assert [negative_fraction]: -frac{1, 3} * 3.0 == -1.0;
  assert [zero_fraction]: frac{0, 7} == 0.0;
};
#end

/-- info:
Obligation: decimal_is_exact
Property: assert
Result: ✅ pass

Obligation: decimal_matches_fraction
Property: assert
Result: ✅ pass

Obligation: nonterminating_fraction
Property: assert
Result: ✅ pass

Obligation: fraction_is_normalized
Property: assert
Result: ✅ pass

Obligation: negative_fraction
Property: assert
Result: ✅ pass

Obligation: zero_fraction
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" realLiterals (options := .quiet)

/-! ## Infix arithmetic and comparisons dispatch to real operations -/

-- Arbitrary real inputs exercise numeric dispatch. True and false
-- comparisons distinguish strict, non-strict and reversed inequalities.
private def realInfixOperators :=
#strata
program Boole;

procedure real_infix_operators(x: real) returns ()
{
  assert [infix_negation]: -x + x == 0.0;
  assert [infix_addition]: x + 0.5 > x;
  assert [infix_subtraction]: x - 0.5 < x;
  assert [infix_multiplication]: x * 2.0 == x + x;
  assert [infix_division]: (x div 2.0) + (x div 2.0) == x;
  assert [infix_less]: x < x + 0.5;
  assert [infix_less_equal]: x <= x + 0.5;
  assert [infix_greater]: x + 0.5 > x;
  assert [infix_greater_equal]: x + 0.5 >= x;
  assert [infix_less_equal_includes_equality]: x <= x;
  assert [infix_greater_equal_includes_equality]: x >= x;
  assert [real_equality]: x == x;
  assert [real_inequality]: x != x + 0.5;
  assert [infix_less_rejects_equality]: !(x < x);
  assert [infix_greater_rejects_equality]: !(x > x);
  assert [infix_less_equal_rejects_greater]: !((x + 0.5) <= x);
  assert [infix_greater_equal_rejects_less]: !(x >= x + 0.5);
};
#end

/-- info:
Obligation: infix_negation
Property: assert
Result: ✅ pass

Obligation: infix_addition
Property: assert
Result: ✅ pass

Obligation: infix_subtraction
Property: assert
Result: ✅ pass

Obligation: infix_multiplication
Property: assert
Result: ✅ pass

Obligation: infix_division
Property: assert
Result: ✅ pass

Obligation: infix_less
Property: assert
Result: ✅ pass

Obligation: infix_less_equal
Property: assert
Result: ✅ pass

Obligation: infix_greater
Property: assert
Result: ✅ pass

Obligation: infix_greater_equal
Property: assert
Result: ✅ pass

Obligation: infix_less_equal_includes_equality
Property: assert
Result: ✅ pass

Obligation: infix_greater_equal_includes_equality
Property: assert
Result: ✅ pass

Obligation: real_equality
Property: assert
Result: ✅ pass

Obligation: real_inequality
Property: assert
Result: ✅ pass

Obligation: infix_less_rejects_equality
Property: assert
Result: ✅ pass

Obligation: infix_greater_rejects_equality
Property: assert
Result: ✅ pass

Obligation: infix_less_equal_rejects_greater
Property: assert
Result: ✅ pass

Obligation: infix_greater_equal_rejects_less
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" realInfixOperators (options := .quiet)

/-! ## Explicit real.* operators inherited from Core -/

-- Named real.* syntax uses separate AST constructors from infix arithmetic.
-- Check each operation and their composition over an arbitrary real input.
private def realNamedOperators :=
#strata
program Boole;

procedure real_named_operators(x: real) returns ()
{
  assert [named_negation]: real.neg(0.5) == -0.5;
  assert [named_addition]: real.add(1.25, 0.5) == 1.75;
  assert [named_subtraction]: real.sub(1.25, 0.5) == 0.75;
  assert [named_multiplication]: real.mul(1.25, 2.0) == 2.5;
  assert [named_division]: real.div(1.5, 2.0) == 0.75;
  assert [named_less]: real.lt(0.5, 1.0);
  assert [named_less_equal]: real.le(0.5, 1.0);
  assert [named_greater]: real.gt(1.0, 0.5);
  assert [named_greater_equal]: real.ge(1.0, 0.5);
  assert [named_less_equal_includes_equality]: real.le(0.5, 0.5);
  assert [named_greater_equal_includes_equality]: real.ge(0.5, 0.5);
  assert [named_less_rejects_equality]: !(real.lt(0.5, 0.5));
  assert [named_greater_rejects_equality]: !(real.gt(0.5, 0.5));
  assert [named_less_equal_rejects_greater]: !(real.le(1.0, 0.5));
  assert [named_greater_equal_rejects_less]: !(real.ge(0.5, 1.0));
  assert [named_operations_compose]: real.div(real.add(x, x), 2.0) == x;
};
#end

/-- info:
Obligation: named_negation
Property: assert
Result: ✅ pass

Obligation: named_addition
Property: assert
Result: ✅ pass

Obligation: named_subtraction
Property: assert
Result: ✅ pass

Obligation: named_multiplication
Property: assert
Result: ✅ pass

Obligation: named_division
Property: assert
Result: ✅ pass

Obligation: named_less
Property: assert
Result: ✅ pass

Obligation: named_less_equal
Property: assert
Result: ✅ pass

Obligation: named_greater
Property: assert
Result: ✅ pass

Obligation: named_greater_equal
Property: assert
Result: ✅ pass

Obligation: named_less_equal_includes_equality
Property: assert
Result: ✅ pass

Obligation: named_greater_equal_includes_equality
Property: assert
Result: ✅ pass

Obligation: named_less_rejects_equality
Property: assert
Result: ✅ pass

Obligation: named_greater_rejects_equality
Property: assert
Result: ✅ pass

Obligation: named_less_equal_rejects_greater
Property: assert
Result: ✅ pass

Obligation: named_greater_equal_rejects_less
Property: assert
Result: ✅ pass

Obligation: named_operations_compose
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" realNamedOperators (options := .quiet)

/-! ## Real computations compose with declarations and contracts -/

-- A function body, requires clause, local initializer, assignment, assertion
-- and ensures clause compose over an arbitrary nonnegative real input.
private def realContracts :=
#strata
program Boole;

function add_half(x: real): real { x + 0.5 }

procedure real_assignment_and_contract(x: real) returns (r: real)
spec {
  requires [nonnegative_input]: x >= 0.0;
  ensures [real_result]: r == x + 0.5;
}
{
  var local: real := add_half(x);
  r := local;
  assert [real_assignment]: r >= 0.5;
};
#end

/-- info:
Obligation: real_assignment
Property: assert
Result: ✅ pass

Obligation: real_result
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" realContracts (options := .quiet)

/-! ## Modified real globals preserve the old-state contract -/

-- A modified global's postcondition refers to its incoming value through
-- old(balance), while its final value reflects the assignment.
private def realModifiedGlobal :=
#strata
program Boole;
var balance: real;
procedure deposit(amount: real) returns ()
spec {
  modifies balance;
  ensures [real_modified_global]: balance == old(balance) + amount;
}
{
  balance := balance + amount;
};
#end

/-- info:
Obligation: real_modified_global
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" realModifiedGlobal (options := .quiet)

/-! ## Real elements survive collection updates and selection -/

-- Exercise the nested types through Core's checker and verifier, including
-- the bounds obligations generated by checked sequence operations.
private def realCollections :=
#strata
program Boole;
procedure real_collections(s: Sequence real, m: Map int real, x: real) returns (r: real)
spec {
  requires [real_sequence_nonempty]: Sequence.length(s) > 0;
  ensures [real_collection_result]: r == x;
}
{
  var updated_s: Sequence real := Sequence.update(s, 0, x);
  var updated_m: Map int real := m[0 := Sequence.select(updated_s, 0)];
  r := updated_m[0];
};
#end

/-- info:
Obligation: init_calls_Sequence.update_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: init_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: real_collection_result
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" realCollections (options := .quiet)

/-! ## Calls and branches carry real arguments and results -/

private def realCallsAndBranches :=
#strata
program Boole;
procedure identity_real(x: real) returns (r: real)
spec { ensures [real_callee_result]: r == x; }
{ r := x; };

procedure choose_real(x: real, choose_positive: bool) returns (r: real)
spec {
  ensures [real_caller_result]: r == (if choose_positive then x else -x);
}
{
  if (choose_positive) {
    call r := identity_real(x);
  } else {
    call r := identity_real(-x);
  }
};
#end

/-- info:
Obligation: real_callee_result
Property: assert
Result: ✅ pass

Obligation: real_caller_result
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" realCallsAndBranches (options := .quiet)

/-! ## Invalid real operations must produce specific diagnostics -/

-- A zero denominator is a lowering error, not a rational constant.
private def zeroDenominator :=
#strata
program Boole;
procedure zero_denominator() returns () {
  assert [invalid_fraction]: frac{1, 0} == 0.0;
};
#end

-- Inspect only the stable diagnostic text; source offsets depend on this file.
#guard match lower zeroDenominator with
  | .error message => (message.splitOn "denominator must be non-zero").length > 1
  | .ok _ => false

-- Core has no Real.Mod operation; report the unsupported operation clearly.
private def realModulo :=
#strata
program Boole;
procedure real_modulo(x: real) returns () {
  assert [invalid_modulo]: x mod 1.0 == 0.0;
};
#end

#guard match lower realModulo with
  | .error message => (message.splitOn "Unsupported real operation: Mod").length > 1
  | .ok _ => false

/-! ## A false real assertion must remain a verification failure -/

-- Successful lowering must still let verification reject a false assertion.
private def falseRealAssertion :=
#strata
program Boole;
procedure false_real_assertion() returns () {
  assert [false_real_sum]: 0.1 + 0.2 == 0.4;
};
#end

/-- info:
Obligation: false_real_sum
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Boole.verify "cvc5" falseRealAssertion (options := .quiet)

/-! ## Existing integer and bitvector dispatch is unchanged -/

-- Real dispatch preserves unbounded integers and modular bitvectors.
private def existingNumericOperators :=
#strata
program Boole;
procedure existing_numeric_operators(x: int) returns () {
  assert [integer_addition_unchanged]: (x + 1) - 1 == x;
  assert [integer_negation_unchanged]: -(-x) == x;
  assert [bitvector_addition_wraps]: bv{8}(255) + bv{8}(1) == bv{8}(0);
  assert [bitvector_negation_wraps]: -bv{8}(1) == bv{8}(255);
};
#end

/-- info:
Obligation: integer_addition_unchanged
Property: assert
Result: ✅ pass

Obligation: integer_negation_unchanged
Property: assert
Result: ✅ pass

Obligation: bitvector_addition_wraps
Property: assert
Result: ✅ pass

Obligation: bitvector_negation_wraps
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Boole.verify "cvc5" existingNumericOperators (options := .quiet)
