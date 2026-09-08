/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: mul_bits_be — the X25519 Montgomery ladder
Source: dalek-lite `curve25519-dalek/src/montgomery.rs`,
`MontgomeryPoint::mul_bits_be` (the constant-time scalar multiplication behind X25519)

Spec in words:  result = u([n]P), where P is the point with u-coordinate `self`
and n is the integer whose big-endian bits are `bits`.

How the proof goes:
- Loop invariant: the two points are [k]P and [k+1]P, where k is the number
  read from the bits so far; which is which is recorded by the previous bit.
- Each step swaps the two points if the bit changed, then one differential
  add-and-double turns ([k]P, [k+1]P) into ([2k]P, [2k+1]P), which is the
  invariant for the next k = 2k + bit.
- When the bits run out, k = n; the final swap puts [n]P first, and as_affine
  reads off its u-coordinate, which is the postcondition.
- Verus needs 547 lines with eleven lemma calls for this; Boole needs the
  invariant and one typing fact. cvc5 proves all 30 obligations; Lean's
  kernel certifies 28 of them.

Verus source (verbatim from dalek-lite):

  #[verifier::rlimit(20)]
  pub fn mul_bits_be(&self, bits: &[bool]) -> (result: MontgomeryPoint)
      requires
          bits.len() <= 255,
          is_valid_montgomery_point(*self),
      ensures
          ({
              // Let P be the canonical affine lift of input u-coordinate
              let P = canonical_montgomery_lift(montgomery_point_as_nat(*self));
              let n = bits_be_as_nat(bits, bits.len() as int);
              let R = montgomery_scalar_mul(P, n);

              // result encodes u([n]P)
              montgomery_point_as_nat(result) == u_coordinate(R)
          }),
  {
      // Algorithm 8 of Costello-Smith 2017
      let affine_u = FieldElement::from_bytes(&self.0);
      let mut x0 = ProjectivePoint::identity();
      let mut x1 = ProjectivePoint { U: affine_u, W: FieldElement::ONE };

      // Go through the bits from most to least significant, using a sliding window of 2
      let mut prev_bit = false;
      let mut i: usize = 0;
      proof {
          // Establish the loop invariant at i = 0.
          // VERIFICATION NOTE: refactoring lemma calls into `assert...by` style breaks rlimit.
          let u0 = montgomery_point_as_nat(*self);
          let P = canonical_montgomery_lift(u0);
          assert(is_valid_u_coordinate(u0));

          // Connect affine_u to u0 (both are the canonical field element decoded from self.0).
          assert(fe51_as_canonical_nat(&affine_u) == u0) by {
              let bytes_nat = u8_32_as_nat(&self.0) % pow2(255);
              assert(fe51_as_nat(&affine_u) == bytes_nat);
              assert(fe51_as_canonical_nat(&affine_u) == bytes_nat % p());
              assert(u0 == field_element_from_bytes(&self.0));
              assert(u0 == bytes_nat % p());
          }

          // Bounds for initial points
          // x0 = (1:0) by ProjectivePoint::identity().
          assert(fe51_limbs_bounded(&x0.U, 51));
          assert(fe51_limbs_bounded(&x0.W, 51));
          lemma_fe51_limbs_bounded_weaken(&x0.U, 51, 52);
          lemma_fe51_limbs_bounded_weaken(&x0.W, 51, 52);
          assert(fe51_limbs_bounded(&x0.U, 52));
          assert(fe51_limbs_bounded(&x0.W, 52));
          assert(fe51_limbs_bounded(&affine_u, 51));

          lemma_one_limbs_bounded_51();
          assert(fe51_limbs_bounded(&x1.W, 51));
          lemma_fe51_limbs_bounded_weaken(&x1.W, 51, 52);
          lemma_fe51_limbs_bounded_weaken(&affine_u, 51, 52);
          assert(fe51_limbs_bounded(&x1.U, 52));
          assert(fe51_limbs_bounded(&x1.W, 52));
          assert(fe51_limbs_bounded(&affine_u, 51));
          assert(is_valid_u_coordinate(fe51_as_canonical_nat(&affine_u)));

          // Scalar invariant at i = 0: k = 0
          assert(bits_be_as_nat(bits, 0) == 0);
          assert(projective_u_coordinate(x0) == 0);
          assert(u_coordinate(montgomery_scalar_mul(P, 0)) == 0);
          assert(projective_u_coordinate(x1) == u0) by {
              // x1 = (affine_u : 1), so its u-coordinate is affine_u.
              lemma_one_field_element_value();
              lemma_field_inv_one();
              assert(fe51_as_canonical_nat(&x1.W) == 1);
              assert(projective_u_coordinate(x1) == field_mul(
                  fe51_as_canonical_nat(&x1.U),
                  field_inv(1),
              ));
              assert(field_inv(1) == 1);
              assert(projective_u_coordinate(x1) == field_mul(fe51_as_canonical_nat(&x1.U), 1));
              lemma_field_mul_one_right(fe51_as_canonical_nat(&x1.U));
              assert(projective_u_coordinate(x1) == fe51_as_canonical_nat(&x1.U) % p());
              assert(fe51_as_canonical_nat(&x1.U) % p() == fe51_as_canonical_nat(&x1.U)) by {
                  let t = fe51_as_nat(&x1.U) % p();
                  assert(fe51_as_canonical_nat(&x1.U) == t);
                  assert(fe51_as_canonical_nat(&x1.U) % p() == t % p());
                  p_gt_2();
                  lemma_mod_division_less_than_divisor(fe51_as_nat(&x1.U) as int, p() as int);
                  assert(t < p());
                  lemma_small_mod(t, p());
                  assert(t % p() == t);
              }
              // x1.U was initialized from affine_u
              assert(x1.U == affine_u);
              assert(projective_u_coordinate(x1) == fe51_as_canonical_nat(&affine_u));
              assert(fe51_as_canonical_nat(&affine_u) == u0);
          }
          assert(u_coordinate(montgomery_scalar_mul(P, 1)) == u0) by {
              // montgomery_scalar_mul(P, 1) = P + [0]P = P
              assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
              assert(montgomery_scalar_mul(P, 1) == montgomery_add(
                  P,
                  montgomery_scalar_mul(P, 0),
              ));
              assert(montgomery_scalar_mul(P, 1) == montgomery_add(
                  P,
                  MontgomeryAffine::Infinity,
              ));
              assert(montgomery_add(P, MontgomeryAffine::Infinity) == P);
              assert(montgomery_scalar_mul(P, 1) == P);
              // P is the canonical lift of u0, so its u-coordinate is u0
              assert(u_coordinate(P) == u0) by {
                  // canonical_montgomery_lift(u0) returns (u0 % p, v), and u0 is already reduced mod p
                  assert(u0 == u0 % p()) by {
                      assert(u0 == field_element_from_bytes(&self.0));
                      let t = u8_32_as_nat(&self.0) % pow2(255);
                      assert(u0 == t % p());
                      assert(u0 % p() == (t % p()) % p());
                      p_gt_2();
                      lemma_mod_division_less_than_divisor(t as int, p() as int);
                      assert((t % p()) < p());
                      lemma_small_mod(t % p(), p());
                      assert((t % p()) % p() == t % p());
                  }
                  assert(u_coordinate(canonical_montgomery_lift(u0)) == u0);
              }
          }

          // Representation invariants needed to instantiate `differential_add_and_double` spec.
          if u0 != 0 {
              // x0 = identity = (1:0) represents ∞ = [0]P.
              assert(projective_represents_montgomery_or_infinity(
                  x0,
                  montgomery_scalar_mul(P, 0),
              ));

              // x1 = (u0:1) represents P = [1]P.
              assert(projective_represents_montgomery_or_infinity(
                  x1,
                  montgomery_scalar_mul(P, 1),
              )) by {
                  assert(montgomery_scalar_mul(P, 1) == P);
                  // Finite points require W != 0 and U = u * W.
                  assert(fe51_as_canonical_nat(&x1.W) == 1) by {
                      lemma_one_field_element_value();
                  }
                  assert(fe51_as_canonical_nat(&x1.W) != 0);
                  assert(fe51_as_canonical_nat(&x1.U) == u0) by {
                      assert(x1.U == affine_u);
                      assert(fe51_as_canonical_nat(&affine_u) == u0);
                  }
                  assert(u_coordinate(P) == u0);
                  assert(fe51_as_canonical_nat(&x1.U) == field_mul(
                      u_coordinate(P),
                      fe51_as_canonical_nat(&x1.W),
                  )) by {
                      lemma_field_mul_one_right(u_coordinate(P));
                  }
              }

              // Establish the ladder invariant at i = 0 (k = 0, prev_bit = false).
              reveal(montgomery_ladder_invariant);
              assert(montgomery_ladder_invariant(x0, x1, P, 0, false));
          }
      }
      // VERIFICATION NOTE: refactoring lemma calls into `assert...by` style breaks rlimit.
      while i < bits.len()
          invariant
              i <= bits.len(),
              // Limb bounds needed for `differential_add_and_double` and `as_affine`
              fe51_limbs_bounded(&x0.U, 52),
              fe51_limbs_bounded(&x0.W, 52),
              fe51_limbs_bounded(&x1.U, 52),
              fe51_limbs_bounded(&x1.W, 52),
              fe51_limbs_bounded(&affine_u, 51),
              // Basepoint decoding/validity (needed for canonical lift reasoning)
              fe51_as_canonical_nat(&affine_u) == montgomery_point_as_nat(*self),
              is_valid_u_coordinate(montgomery_point_as_nat(*self)),
              is_valid_u_coordinate(fe51_as_canonical_nat(&affine_u)),
              // Scalar-multiplication relationship (Montgomery ladder invariant)
              ({
                  let u0 = montgomery_point_as_nat(*self);
                  if u0 == 0 {
                      // Degenerate case: u0=0 is the (0,0) 2-torsion point; all multiples have u=0.
                      &&& projective_u_coordinate(x0) == 0
                      &&& projective_u_coordinate(x1) == 0
                  } else {
                      let P = canonical_montgomery_lift(u0);
                      let k = bits_be_as_nat(bits, i as int);
                      montgomery_ladder_invariant(x0, x1, P, k, prev_bit)
                  }
              }),
          decreases bits.len() - i,
      {
          let cur_bit = bits[i];
          let choice: u8 = (prev_bit ^ cur_bit) as u8;
          // VERIFICATION: extracted from inline `choice.into()` to name the Choice for proof
          let swap_choice = Choice::from(choice);

          #[cfg(not(verus_keep_ghost))]
          debug_assert!(choice == 0 || choice == 1);

          let ghost x0_before_swap = x0;
          let ghost x1_before_swap = x1;
          conditional_swap_montgomery_projective(&mut x0, &mut x1, swap_choice);
          proof {
              let u0 = montgomery_point_as_nat(*self);
              let k = bits_be_as_nat(bits, i as int);

              // Connect affine_u to u0
              assert(fe51_as_canonical_nat(&affine_u) == u0);

              if u0 == 0 {
                  // In the degenerate u0=0 case, the loop invariant only tracks that both
                  // projective u-coordinates are 0, and conditional_swap preserves this.
                  assert(projective_u_coordinate(x0_before_swap) == 0);
                  assert(projective_u_coordinate(x1_before_swap) == 0);
                  assert(projective_u_coordinate(x0) == 0);
                  assert(projective_u_coordinate(x1) == 0);
              } else {
                  let P = canonical_montgomery_lift(u0);

                  // Representation facts from the loop invariant (before the swap).
                  assert(montgomery_ladder_invariant(
                      x0_before_swap,
                      x1_before_swap,
                      P,
                      k,
                      prev_bit,
                  ));

                  // Determine whether the swap occurred: swap iff (prev_bit ^ cur_bit)
                  let swapped_now = prev_bit ^ cur_bit;
                  if swapped_now {
                      assert(choice == 1u8);
                      assert(choice_is_true(swap_choice));
                      // From conditional_swap spec: x0 = old(x1), x1 = old(x0)
                      assert(x0.U == x1_before_swap.U);
                      assert(x0.W == x1_before_swap.W);
                      assert(x1.U == x0_before_swap.U);
                      assert(x1.W == x0_before_swap.W);
                  } else {
                      assert(choice == 0u8);
                      assert(!choice_is_true(swap_choice));
                      // No swap: x0,x1 unchanged
                      assert(x0.U == x0_before_swap.U);
                      assert(x0.W == x0_before_swap.W);
                      assert(x1.U == x1_before_swap.U);
                      assert(x1.W == x1_before_swap.W);
                  }

                  // After the swap, the invariant switches from prev_bit to cur_bit.
                  if swapped_now {
                      // swapped_now == (prev_bit ^ cur_bit) means cur_bit == !prev_bit
                      assert(cur_bit == !prev_bit) by {
                          assert(swapped_now == (prev_bit ^ cur_bit));
                      }
                      crate::lemmas::montgomery_lemmas::lemma_ladder_invariant_swap(
                          x0_before_swap,
                          x1_before_swap,
                          P,
                          k,
                          prev_bit,
                      );
                      assert(montgomery_ladder_invariant(
                          x1_before_swap,
                          x0_before_swap,
                          P,
                          k,
                          !prev_bit,
                      ));
                      // conditional_swap: x0 = old(x1), x1 = old(x0)
                      assert(x0 == x1_before_swap) by {
                          assert(x0.U == x1_before_swap.U);
                          assert(x0.W == x1_before_swap.W);
                      }
                      assert(x1 == x0_before_swap) by {
                          assert(x1.U == x0_before_swap.U);
                          assert(x1.W == x0_before_swap.W);
                      }
                      assert(montgomery_ladder_invariant(x0, x1, P, k, cur_bit));
                  } else {
                      // swapped_now == false means cur_bit == prev_bit, and no swap occurred.
                      assert(cur_bit == prev_bit) by {
                          assert(swapped_now == (prev_bit ^ cur_bit));
                      }
                      assert(x0 == x0_before_swap) by {
                          assert(x0.U == x0_before_swap.U);
                          assert(x0.W == x0_before_swap.W);
                      }
                      assert(x1 == x1_before_swap) by {
                          assert(x1.U == x1_before_swap.U);
                          assert(x1.W == x1_before_swap.W);
                      }
                      assert(montgomery_ladder_invariant(x0, x1, P, k, cur_bit));
                  }

              }

              // The call to `differential_add_and_double` below is justified by the limb-bound
              // invariants on x0/x1 and affine_u.
          }
          proof {
              // Prepare the antecedents needed to instantiate the postconditions of
              // `differential_add_and_double` (Cases 1 and 2 depend on the old(P)/old(Q) representations).
              let u0 = montgomery_point_as_nat(*self);
              if u0 != 0 {
                  let P = canonical_montgomery_lift(u0);
                  let k = bits_be_as_nat(bits, i as int);
                  // After the conditional swap, (x0, x1) satisfy ladder_invariant with `cur_bit`.
                  assert(montgomery_ladder_invariant(x0, x1, P, k, cur_bit));
                  reveal(montgomery_ladder_invariant);
                  if cur_bit {
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, k + 1),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, k),
                      ));
                  } else {
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, k),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, k + 1),
                      ));
                  }
              }
          }
          let ghost x0_before_dad = x0;
          let ghost x1_before_dad = x1;
          differential_add_and_double(&mut x0, &mut x1, &affine_u);

          prev_bit = cur_bit;
          i = i + 1;
          proof {
              // Re-establish the full loop invariant for the next iteration.
              let u0 = montgomery_point_as_nat(*self);
              let P = canonical_montgomery_lift(u0);
              let k = bits_be_as_nat(bits, (i - 1) as int);

              let base = canonical_montgomery_lift(fe51_as_canonical_nat(&affine_u));
              assert(base == P);

              if u0 == 0 {
                  // Use the degenerate-case postcondition of `differential_add_and_double`:
                  // if u(P-Q)=0 and both inputs have u=0, both outputs have u=0.
                  assert(fe51_as_canonical_nat(&affine_u) == 0);
                  assert(projective_u_coordinate(x0_before_dad) == 0);
                  assert(projective_u_coordinate(x1_before_dad) == 0);
                  assert(projective_u_coordinate(x0) == 0);
                  assert(projective_u_coordinate(x1) == 0);
              } else {
                  // Instantiate the ladder-step postcondition of `differential_add_and_double`.
                  assert(fe51_as_canonical_nat(&affine_u) != 0);

                  if cur_bit {
                      // Case 2: inputs were swapped: ([k+1]P, [k]P) -> ([2k+2]P, [2k+1]P)
                      // Use Case 2 postcondition of differential_add_and_double
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, 2nat * k + 2nat),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, 2nat * k + 1nat),
                      ));
                  } else {
                      // Case 1: inputs in order: ([k]P, [k+1]P) -> ([2k]P, [2k+1]P)
                      // Use Case 1 postcondition of differential_add_and_double
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, 2nat * k),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, 2nat * k + 1nat),
                      ));
                  }
              }

              // bits_be_as_nat update: k_next = 2*k + b
              let b = if cur_bit {
                  1nat
              } else {
                  0nat
              };
              assert(bits_be_as_nat(bits, i as int) == b + 2nat * k);
              // Re-establish ladder_invariant at the updated k (i has been incremented) and prev_bit.
              if u0 != 0 {
                  let k_next = bits_be_as_nat(bits, i as int);
                  // k_next == 2*k + b
                  assert(k_next == b + 2nat * k);
                  reveal(montgomery_ladder_invariant);
                  if prev_bit {
                      // x0 = [k_next+1]P and x1 = [k_next]P
                      assert(cur_bit);
                      assert(b == 1nat);
                      assert(k_next == 2nat * k + 1nat);
                      assert(k_next + 1 == 2nat * k + 2nat);
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, 2nat * k + 2nat),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, 2nat * k + 1nat),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, k_next + 1),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, k_next),
                      ));
                  } else {
                      // x0 = [k_next]P and x1 = [k_next+1]P
                      assert(!cur_bit);
                      assert(b == 0nat);
                      assert(k_next == 2nat * k);
                      assert(k_next + 1 == 2nat * k + 1nat);
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, 2nat * k),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, 2nat * k + 1nat),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x0,
                          montgomery_scalar_mul(P, k_next),
                      ));
                      assert(projective_represents_montgomery_or_infinity(
                          x1,
                          montgomery_scalar_mul(P, k_next + 1),
                      ));
                  }
                  assert(montgomery_ladder_invariant(x0, x1, P, k_next, prev_bit));
              }
          }
      }
      // The final value of prev_bit above is scalar.bits()[0], i.e., the LSB of scalar
      let ghost x0_before_final_swap = x0;
      let ghost x1_before_final_swap = x1;
      let ghost saved_prev_bit = prev_bit;  // save before zeroize for proof
      // VERIFICATION: rewritten from `Choice::from(prev_bit as u8)` because Verus
      // cannot reason about `bool as u8`; if-expression is equivalent
      let final_choice_u8: u8 = if prev_bit {
          1u8
      } else {
          0u8
      };
      let final_swap_choice = Choice::from(final_choice_u8);
      conditional_swap_montgomery_projective(&mut x0, &mut x1, final_swap_choice);
      // Don't leave the bit in the stack
      #[cfg(feature = "zeroize")]
      zeroize_bool(&mut prev_bit);

      proof {
          // After the final conditional swap, x0 encodes u([n]P) where n is the full bitstring.
          let u0 = montgomery_point_as_nat(*self);
          let P = canonical_montgomery_lift(u0);
          let n = bits_be_as_nat(bits, bits.len() as int);

          // Connect saved_prev_bit to final_swap_choice.
          // From Choice::from spec: (u == 1) == choice_is_true(Choice::from(u))
          // Note: use saved_prev_bit since prev_bit may have been zeroized
          assert(choice_is_true(final_swap_choice) == saved_prev_bit);

          if u0 == 0 {
              // In the u0=0 degenerate case, both sides are 0.
              assert(projective_u_coordinate(x0) == 0);
              lemma_u_coordinate_scalar_mul_canonical_lift_zero(n);
              assert(u_coordinate(montgomery_scalar_mul(P, n)) == 0);
              assert(projective_u_coordinate(x0) == u_coordinate(montgomery_scalar_mul(P, n)));
          } else {
              // The final swap ensures x0 holds [n]P regardless of saved_prev_bit.
              // From loop invariant, we have projective_represents_montgomery_or_infinity
              // for x0_before_final_swap or x1_before_final_swap (depending on saved_prev_bit).
              // Note: use saved_prev_bit since prev_bit may have been zeroized
              reveal(montgomery_ladder_invariant);
              if saved_prev_bit {
                  assert(x0.U == x1_before_final_swap.U);
                  assert(x0.W == x1_before_final_swap.W);
                  // x1_before_final_swap represents [n]P
                  assert(projective_represents_montgomery_or_infinity(
                      x1_before_final_swap,
                      montgomery_scalar_mul(P, n),
                  ));
                  assert(projective_represents_montgomery_or_infinity(
                      x1_before_final_swap,
                      montgomery_scalar_mul(P, n),
                  ));
                  // After swap, x0 has the same coordinates, so also represents [n]P
                  assert(projective_represents_montgomery_or_infinity(
                      x0,
                      montgomery_scalar_mul(P, n),
                  ));
              } else {
                  assert(x0.U == x0_before_final_swap.U);
                  assert(x0.W == x0_before_final_swap.W);
                  // x0_before_final_swap represents [n]P
                  assert(projective_represents_montgomery_or_infinity(
                      x0_before_final_swap,
                      montgomery_scalar_mul(P, n),
                  ));
                  assert(projective_represents_montgomery_or_infinity(
                      x0_before_final_swap,
                      montgomery_scalar_mul(P, n),
                  ));
                  // No swap, x0 still represents [n]P
                  assert(projective_represents_montgomery_or_infinity(
                      x0,
                      montgomery_scalar_mul(P, n),
                  ));
              }
              // Use lemma to get u-coordinate equality
              lemma_projective_represents_implies_u_coordinate(x0, montgomery_scalar_mul(P, n));
              // The lemma gives: projective_u_coordinate(x0) == (u_coordinate(...) % p())
              // For canonical points, u-coordinates are already < p, so % p() is identity.
              lemma_canonical_scalar_mul_u_coord_reduced(u0, n);
              let u_coord = u_coordinate(montgomery_scalar_mul(P, n));
              assert(u_coord < p());
              assert(u_coord % p() == u_coord) by {
                  lemma_small_mod(u_coord, p());
              }
              assert(projective_u_coordinate(x0) == u_coordinate(montgomery_scalar_mul(P, n)));
          }
          // Bounds needed for as_affine
          assert(fe51_limbs_bounded(&x0.U, 52));
          assert(fe51_limbs_bounded(&x0.W, 52));
          lemma_fe51_limbs_bounded_weaken(&x0.U, 52, 54);
          lemma_fe51_limbs_bounded_weaken(&x0.W, 52, 54);
          assert(fe51_limbs_bounded(&x0.U, 54));
          assert(fe51_limbs_bounded(&x0.W, 54));
      }
      let result = x0.as_affine();
      proof {
          // Discharge the function postcondition.
          let u0 = montgomery_point_as_nat(*self);
          let P = canonical_montgomery_lift(u0);
          let n = bits_be_as_nat(bits, bits.len() as int);
          // as_affine returns the affine u-coordinate of x0
          assert(montgomery_point_as_nat(result) == projective_u_coordinate(x0));
          // From loop invariant at exit and final conditional swap, x0 encodes u([n]P)
          assert(projective_u_coordinate(x0) == u_coordinate(montgomery_scalar_mul(P, n)));
      }
      result
  }

-/

/-
Boole encoding: from the verus-boogie translation of the `montgomery` module
(Cheng's `verus-lean boole`), with one departure for the Lean path: the point and
field-element types are uninterpreted sorts, because the translator emits them as
datatypes over limb sequences, which the SMT→Lean bridge cannot declare
(strata-org/Strata#1472).  Everything abstracted is marked below.
-/
private def montgomeryLadderSeed : StrataDDM.Program :=
#strata
program Boole;

// Uninterpreted sorts for the translation's datatypes: FieldElement51 (5 u64 limbs),
// montgomery::ProjectivePoint { U, W }, MontgomeryPoint([u8; 32]), the spec type
// MontgomeryAffine (Infinity | Finite { u, v }), and subtle::Choice.
type FieldElement;
type ProjectivePoint;
type MontgomeryPoint;
type MontgomeryAffine;
type Choice;

// The Verus spec functions over them, uninterpreted; the proof uses them by congruence only.
function fe51_as_canonical_nat(fe: FieldElement) : int;
function montgomery_point_as_nat(point: MontgomeryPoint) : int;
function is_valid_u_coordinate(u: int) : bool;
function is_valid_montgomery_point(point: MontgomeryPoint) : bool {
  is_valid_u_coordinate(montgomery_point_as_nat(point))
}
function canonical_montgomery_lift(u: int) : MontgomeryAffine;
function montgomery_infinity() : MontgomeryAffine;
function montgomery_add(P: MontgomeryAffine, Q: MontgomeryAffine) : MontgomeryAffine;
function u_coordinate(point: MontgomeryAffine) : int;
function projective_u_coordinate(P: ProjectivePoint) : int;
function projective_represents_montgomery_or_infinity(P_proj: ProjectivePoint, P_aff: MontgomeryAffine) : bool;
function choice_is_true(c: Choice) : bool;
// n mod p, p = 2^255 - 19; kept as a function so the mod never reaches lean-smt.
function field_canonical(n: int) : int { n mod 57896044618658097711785492504343953926634992332820282019728792003956564819949 }

// Verus montgomery_scalar_mul: [n]P by repeated addition.  The solver sees it only by
// name; the first two axioms are its definition, the third is the Infinity case of the
// Verus montgomery_add.
rec function montgomery_scalar_mul(P: MontgomeryAffine, n: int) : MontgomeryAffine
  decreases n
{
  if n <= 0 then montgomery_infinity() else montgomery_add(P, montgomery_scalar_mul(P, n - 1))
}
;
axiom (∀ P: MontgomeryAffine . montgomery_scalar_mul(P, 0) == montgomery_infinity());
axiom (∀ P: MontgomeryAffine, n: int . n > 0 ==> montgomery_scalar_mul(P, n) == montgomery_add(P, montgomery_scalar_mul(P, n - 1)));
axiom (∀ P: MontgomeryAffine . montgomery_add(P, montgomery_infinity()) == P);

// Verus bits_be_as_nat: the number whose big-endian bits are bits[0..len).  First axiom:
// the nat typing of the result (>= 0); the other two are its definition.
rec function bits_be_as_nat(bits: Sequence bool, len: int) : int
  requires 0 <= len && len <= Sequence.length(bits);
  decreases len
{
  if len <= 0 then 0 else (if Sequence.select(bits, len - 1) then 1 else 0) + 2 * bits_be_as_nat(bits, len - 1)
}
;
axiom (∀ bits: Sequence bool, len: int . 0 <= bits_be_as_nat(bits, len));
axiom (∀ bits: Sequence bool . bits_be_as_nat(bits, 0) == 0);
axiom (∀ bits: Sequence bool, len: int . 0 < len && len <= Sequence.length(bits) ==> bits_be_as_nat(bits, len) == (if Sequence.select(bits, len - 1) then 1 else 0) + 2 * bits_be_as_nat(bits, len - 1));

// Verus montgomery_ladder_invariant (opaque there, revealed in the proof): x0 = [k]P and
// x1 = [k+1]P, or swapped when bit is set.  The case split is at the top level so the
// solver sees montgomery_scalar_mul(P, k) and montgomery_scalar_mul(P, k + 1) as terms.
function montgomery_ladder_invariant(x0: ProjectivePoint, x1: ProjectivePoint, P: MontgomeryAffine, k: int, bit: bool) : bool {
  if bit
  then projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k + 1)) &&
       projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k))
  else projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k)) &&
       projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k + 1))
}

// The three curve lemmas the Verus proof calls after the loop, plus vstd's lemma_small_mod,
// as axioms (the translation makes them assume-false stubs).
// lemma_projective_represents_implies_u_coordinate
axiom (∀ P_proj: ProjectivePoint, P_aff: MontgomeryAffine .
  projective_represents_montgomery_or_infinity(P_proj, P_aff) ==>
  projective_u_coordinate(P_proj) == field_canonical(u_coordinate(P_aff)));
// lemma_small_mod (vstd), as called by the Verus proof
axiom (∀ x: int . 0 <= x && x < 57896044618658097711785492504343953926634992332820282019728792003956564819949 ==> field_canonical(x) == x);
// lemma_u_coordinate_scalar_mul_canonical_lift_zero
axiom (∀ n: int . n >= 0 ==> u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(0), n)) == 0);
// lemma_canonical_scalar_mul_u_coord_reduced (with u_coordinate : nat)
axiom (∀ u0: int, n: int . u0 != 0 && n >= 0 ==>
  0 <= u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(u0), n)) &&
  u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(u0), n)) < 57896044618658097711785492504343953926634992332820282019728792003956564819949);

// Callee contracts: the Verus ensures of each callee, minus limb bounds; the callees are
// verified separately in dalek-lite.
// FieldElement::from_bytes(&self.0)
procedure FieldElement_from_bytes(bytes: MontgomeryPoint) returns (r: FieldElement)
spec {
  ensures fe51_as_canonical_nat(r) == montgomery_point_as_nat(bytes);
}
{ assume false; };

// ProjectivePoint::identity(): U = 1, W = 0, which represents Infinity.
procedure ProjectivePoint_identity() returns (r: ProjectivePoint)
spec {
  ensures projective_u_coordinate(r) == 0;
  ensures projective_represents_montgomery_or_infinity(r, montgomery_infinity());
}
{ assume false; };

// ProjectivePoint { U: affine_u, W: FieldElement::ONE }: represents the lift of u
// (what the Verus proof derives for it).
procedure ProjectivePoint_from_affine_u(affine_u: FieldElement) returns (r: ProjectivePoint)
spec {
  ensures projective_u_coordinate(r) == fe51_as_canonical_nat(affine_u);
  ensures fe51_as_canonical_nat(affine_u) != 0 ==>
    projective_represents_montgomery_or_infinity(r, canonical_montgomery_lift(fe51_as_canonical_nat(affine_u)));
}
{ assume false; };

// Choice::from(u8) (subtle_assumes)
procedure Choice_from(u: int) returns (c: Choice)
spec {
  ensures (u == 1) == choice_is_true(c);
}
{ assume false; };

// conditional_swap_montgomery_projective (subtle_assumes): constant-time swap.
procedure conditional_swap_montgomery_projective(a: ProjectivePoint, b: ProjectivePoint, choice: Choice) returns (a_out: ProjectivePoint, b_out: ProjectivePoint)
spec {
  ensures !choice_is_true(choice) ==> a_out == a && b_out == b;
  ensures choice_is_true(choice) ==> a_out == b && b_out == a;
}
{ assume false; };

// differential_add_and_double: one ladder step; the two ∀k clauses are the Verus ones.
procedure differential_add_and_double(P: ProjectivePoint, Q: ProjectivePoint, affine_PmQ: FieldElement) returns (P_out: ProjectivePoint, Q_out: ProjectivePoint)
spec {
  requires is_valid_u_coordinate(fe51_as_canonical_nat(affine_PmQ));
  ensures (fe51_as_canonical_nat(affine_PmQ) == 0 && projective_u_coordinate(P) == 0 && projective_u_coordinate(Q) == 0) ==>
    (projective_u_coordinate(P_out) == 0 && projective_u_coordinate(Q_out) == 0);
  ensures ∀ k: int . k >= 0 && fe51_as_canonical_nat(affine_PmQ) != 0 &&
    projective_represents_montgomery_or_infinity(P, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), k)) &&
    projective_represents_montgomery_or_infinity(Q, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), k + 1)) ==>
    projective_represents_montgomery_or_infinity(P_out, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), 2 * k)) &&
    projective_represents_montgomery_or_infinity(Q_out, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), 2 * k + 1));
  ensures ∀ k: int . k >= 0 && fe51_as_canonical_nat(affine_PmQ) != 0 &&
    projective_represents_montgomery_or_infinity(P, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), k + 1)) &&
    projective_represents_montgomery_or_infinity(Q, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), k)) ==>
    projective_represents_montgomery_or_infinity(P_out, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), 2 * k + 2)) &&
    projective_represents_montgomery_or_infinity(Q_out, montgomery_scalar_mul(canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ)), 2 * k + 1));
}
{ assume false; };

// zeroize_bool (core_assumes)
procedure zeroize_bool(b: bool) returns (b_out: bool)
spec {
  ensures b_out == false;
}
{ assume false; };

// ProjectivePoint::as_affine: U / W, i.e. projective_u_coordinate.
procedure as_affine(self: ProjectivePoint) returns (result: MontgomeryPoint)
spec {
  ensures montgomery_point_as_nat(result) == projective_u_coordinate(self);
}
{ assume false; };

procedure mul_bits_be(self: MontgomeryPoint, bits: Sequence bool) returns (result: MontgomeryPoint)
spec {
  // Precondition (Verus): at most 255 bits.
  requires Sequence.length(bits) <= 255;

  // Precondition (Verus): self is a valid u-coordinate, i.e. some point has it.
  requires is_valid_montgomery_point(self);

  // Postcondition (Verus): the result is the u-coordinate of [n]P, for P the point with
  // u-coordinate self and n the number read from the bits.
  ensures montgomery_point_as_nat(result) ==
    u_coordinate(montgomery_scalar_mul(canonical_montgomery_lift(montgomery_point_as_nat(self)), bits_be_as_nat(bits, Sequence.length(bits))));
}
{
  var affine_u: FieldElement;
  var x0: ProjectivePoint;
  var x1: ProjectivePoint;
  var prev_bit: bool;
  var cur_bit: bool;
  var i: int;
  var choice: int;
  var swap_choice: Choice;
  var final_choice_u8: int;
  var final_swap_choice: Choice;
  call affine_u := FieldElement_from_bytes(self);
  call x0 := ProjectivePoint_identity();
  call x1 := ProjectivePoint_from_affine_u(affine_u);
  prev_bit := false;
  i := 0;
  while (i < Sequence.length(bits))
    decreases Sequence.length(bits) - i
    invariant 0 <= i && i <= Sequence.length(bits)

    // The ladder invariant (Verus), minus limb bounds and facts about unmodified variables.
    // u = 0 is the 2-torsion point (0, 0): all its multiples have u = 0.
    invariant if montgomery_point_as_nat(self) == 0
      then projective_u_coordinate(x0) == 0 && projective_u_coordinate(x1) == 0
      else montgomery_ladder_invariant(x0, x1, canonical_montgomery_lift(montgomery_point_as_nat(self)), bits_be_as_nat(bits, i), prev_bit)
  {
    cur_bit := Sequence.select(bits, i);
    choice := if (prev_bit != cur_bit) then 1 else 0;
    call swap_choice := Choice_from(choice);
    call x0, x1 := conditional_swap_montgomery_projective(x0, x1, swap_choice);
    call x0, x1 := differential_add_and_double(x0, x1, affine_u);
    prev_bit := cur_bit;
    i := i + 1;
  }
  final_choice_u8 := if prev_bit then 1 else 0;
  call final_swap_choice := Choice_from(final_choice_u8);
  call x0, x1 := conditional_swap_montgomery_projective(x0, x1, final_swap_choice);
  call prev_bit := zeroize_bool(prev_bit);
  call result := as_affine(x0);
};

#end

/-- info:
Obligation: montgomery_scalar_mul_terminates_0
Property: assert
Result: ✅ pass

Obligation: montgomery_scalar_mul_terminates_1
Property: assert
Result: ✅ pass

Obligation: bits_be_as_nat_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bits_be_as_nat_body_calls_bits_be_as_nat_1
Property: assert
Result: ✅ pass

Obligation: bits_be_as_nat_terminates_0
Property: assert
Result: ✅ pass

Obligation: bits_be_as_nat_terminates_1
Property: assert
Result: ✅ pass

Obligation: FieldElement_from_bytes_ensures_11_33166
Property: assert
Result: ✅ pass

Obligation: ProjectivePoint_identity_ensures_13_33404
Property: assert
Result: ✅ pass

Obligation: ProjectivePoint_identity_ensures_14_33447
Property: assert
Result: ✅ pass

Obligation: ProjectivePoint_from_affine_u_ensures_16_33776
Property: assert
Result: ✅ pass

Obligation: ProjectivePoint_from_affine_u_ensures_17_33849
Property: assert
Result: ✅ pass

Obligation: Choice_from_ensures_19_34129
Property: assert
Result: ✅ pass

Obligation: conditional_swap_montgomery_projective_ensures_21_34441
Property: assert
Result: ✅ pass

Obligation: conditional_swap_montgomery_projective_ensures_22_34505
Property: assert
Result: ✅ pass

Obligation: differential_add_and_double_ensures_25_34918
Property: assert
Result: ✅ pass

Obligation: differential_add_and_double_ensures_26_35125
Property: assert
Result: ✅ pass

Obligation: differential_add_and_double_ensures_27_35796
Property: assert
Result: ✅ pass

Obligation: zeroize_bool_ensures_29_36585
Property: assert
Result: ✅ pass

Obligation: as_affine_ensures_31_36785
Property: assert
Result: ✅ pass

Obligation: mul_bits_be_post_mul_bits_be_ensures_35_37352_calls_bits_be_as_nat_0
Property: assert
Result: ✅ pass

Obligation: loop_invariant_calls_bits_be_as_nat_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_45_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_45_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_45
Property: assert
Result: ✅ pass

Obligation: set_cur_bit_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_differential_add_and_double_requires_24_34849_25
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_45_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_45_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_45
Property: assert
Result: ✅ pass

Obligation: mul_bits_be_ensures_35_37352
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" montgomeryLadderSeed (options := .quiet)

-- Lean backend (lean-smt: cvc5 proofs replayed in the Lean kernel).
-- 28 of the 30 obligations are certified.  The remaining two (loop-invariant preservation
-- and the final postcondition) are proved by cvc5 (Level 2) but lean-smt cannot replay
-- those proofs: the field prime p = 2^255-19 enters cvc5's arithmetic steps as a rational
-- coefficient 1/p, which lean-smt's reconstruction does not support.  Open item.
example : Strata.smtVCsCorrectBoole montgomeryLadderSeed := by
  gen_smt_vcs_boole
  all_goals (try smt (timeout := .some 30))
  all_goals sorry
