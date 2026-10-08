module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_WEIGHT_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def truncatedDyadicLength (N j : ℕ) : ℕ := min (2^j) (N-2^j)

theorem truncatedDyadicLength_le_width (N j : ℕ) :
    truncatedDyadicLength N j ≤ 2^j := min_le_left _ _

theorem truncatedDyadic_start_lt {N j : ℕ} (hj : j < Nat.clog 2 N) :
    2^j < N := Nat.pow_lt_of_lt_clog hj

theorem truncatedDyadic_endpoint_le {N j : ℕ} (hj : j < Nat.clog 2 N) :
    2^j+truncatedDyadicLength N j ≤ N := by
  have hs := truncatedDyadic_start_lt hj
  have hl : truncatedDyadicLength N j ≤ N-2^j := min_le_right _ _
  omega

theorem truncatedDyadicLength_pos {N j : ℕ} (hj : j < Nat.clog 2 N) :
    0 < truncatedDyadicLength N j := by
  have hs := truncatedDyadic_start_lt hj
  have hp : 0 < (2:ℕ)^j := pow_pos (by norm_num) _
  unfold truncatedDyadicLength
  omega

theorem truncatedDyadicLength_eq_width {N j : ℕ} (hj : 2^(j+1) ≤ N) :
    truncatedDyadicLength N j = 2^j := by
  rw [pow_succ] at hj
  unfold truncatedDyadicLength
  omega

theorem sum_range_min_pow_eq_truncatedDyadic {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {N : ℕ} (hN : 0 < N) (J : ℕ) :
    (∑ i ∈ Finset.range (min N (2^J)), f i) =
      f 0+∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (truncatedDyadicLength N j), f (2^j+i) := by
  induction J with
  | zero => simp [min_eq_right (show (1:ℕ) ≤ N by omega)]
  | succ J ih =>
    rw [Finset.sum_range_succ,← add_assoc,← ih]
    by_cases hJ : 2^J ≤ N
    · have he : min N (2^(J+1)) = 2^J+truncatedDyadicLength N J := by
        rw [pow_succ]
        unfold truncatedDyadicLength
        omega
      rw [he,min_eq_right hJ,Finset.sum_range_add]
    · have hlt : N < 2^J := by omega
      have hnext : N ≤ 2^(J+1) := by
        rw [pow_succ]
        omega
      have hz : truncatedDyadicLength N J = 0 := by
        unfold truncatedDyadicLength
        omega
      rw [min_eq_left hlt.le,min_eq_left hnext,hz]
      simp

theorem sum_range_eq_truncatedDyadic {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (hf : f 0 = 0) (N : ℕ) :
    (∑ i ∈ Finset.range N, f i) =
      ∑ j ∈ Finset.range (Nat.clog 2 N),
        ∑ i ∈ Finset.range (truncatedDyadicLength N j), f (2^j+i) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have h := sum_range_min_pow_eq_truncatedDyadic f (Nat.pos_of_ne_zero hN) (Nat.clog 2 N)
    simpa only [min_eq_left (Nat.le_pow_clog (by norm_num : 1 < (2:ℕ)) N),hf,zero_add] using h

end MathCollab.Density.Stronger.Atkinson
