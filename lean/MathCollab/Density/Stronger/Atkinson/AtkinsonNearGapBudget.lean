module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSeparatedReciprocal
public import MathCollab.Density.Stronger.Atkinson.AtkinsonGapArithmetic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonFarGapRow (H : ℝ) (M : ℕ) (W : Finset ℝ) (t : ℝ) : ℝ :=
  ∑ u ∈ W with Real.sqrt (H*(M:ℝ)) < |u-t|,
    atkinsonPrefixGapMajorant M M t u

def atkinsonNearRowBound (H G : ℝ) (M : ℕ) : ℝ :=
  (M:ℝ)+120*Real.sqrt (H*(M:ℝ))/G*
    (harmonic (Nat.ceil (Real.sqrt (H*(M:ℝ))/G)):ℝ)

theorem atkinson_near_gap_row_le {H G : ℝ} {M : ℕ} {W : Finset ℝ} {t : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hM : 0 < M) (hSep : IsSeparated G W)
    (ht : t ∈ W) (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H) :
    (∑ u ∈ W with u ≠ t ∧ |u-t| ≤ Real.sqrt (H*(M:ℝ)),
      atkinsonPrefixGapMajorant M M t u) ≤
      120*Real.sqrt (H*(M:ℝ))/G*
        (harmonic (Nat.ceil (Real.sqrt (H*(M:ℝ))/G)):ℝ) := by
  classical
  let S := W.filter (fun u => u ≠ t ∧ |u-t| ≤ Real.sqrt (H*(M:ℝ)))
  have hi := atkinson_sum_inv_gap_le_harmonic_ceil (S := S)
    (L := Real.sqrt (H*(M:ℝ))) hG hSep ht
    (Finset.filter_subset (s := W) _) (fun u hu => (Finset.mem_filter.mp hu).2)
  have hb : (∑ u ∈ S, atkinsonPrefixGapMajorant M M t u) ≤
      60*Real.sqrt (H*(M:ℝ))*∑ u ∈ S, 1/|u-t| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hd := Finset.mem_filter.mp hu
    have hg := atkinsonPrefixGapMajorant_le_near hH
      (hrange t ht).1 (hrange t ht).2 (hrange u hd.1).1 (hrange u hd.1).2
      hd.2.1.symm hM (by simpa only [abs_sub_comm] using hd.2.2)
    simpa only [abs_sub_comm, div_eq_mul_inv, one_mul] using hg
  have hm := mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ 60*Real.sqrt (H*(M:ℝ)))
  exact (hb.trans hm).trans_eq (by ring)

theorem atkinson_gap_row_le_near_add_far {H G : ℝ} {M : ℕ} {W : Finset ℝ} {t : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hM : 0 < M) (hSep : IsSeparated G W)
    (ht : t ∈ W) (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H) :
    (∑ u ∈ W, atkinsonPrefixGapMajorant M M t u) ≤
      atkinsonNearRowBound H G M+atkinsonFarGapRow H M W t := by
  classical
  have hs : (∑ u ∈ W, atkinsonPrefixGapMajorant M M t u) =
      (∑ u ∈ W, if u = t then (M:ℝ) else 0)+
      (∑ u ∈ W with u ≠ t ∧ |u-t| ≤ Real.sqrt (H*(M:ℝ)),
        atkinsonPrefixGapMajorant M M t u)+atkinsonFarGapRow H M W t := by
    unfold atkinsonFarGapRow
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases he : u = t
    · subst u
      simp only [atkinsonPrefixGapMajorant_self, sub_self, abs_zero,
        ne_self_iff_false, false_and, ite_false, ite_true, add_zero,
        not_lt.mpr (Real.sqrt_nonneg (H*(M:ℝ)))]
    · by_cases hg : |u-t| ≤ Real.sqrt (H*(M:ℝ))
      · simp only [ne_eq, he, not_false_eq_true, true_and, hg, not_lt.mpr hg,
          ite_true, ite_false, zero_add, add_zero]
      · simp only [ne_eq, he, not_false_eq_true, true_and, hg, lt_of_not_ge hg,
          ite_true, ite_false, zero_add]
  have hd : (∑ u ∈ W, if u = t then (M:ℝ) else 0) = (M:ℝ) := by simp [ht]
  rw [hd] at hs
  have hn := atkinson_near_gap_row_le hH hG hM hSep ht hrange
  unfold atkinsonNearRowBound
  linarith

theorem atkinson_gap_double_sum_le_near_add_far {H G : ℝ} {M : ℕ} {W : Finset ℝ}
    (hH : 0 < H) (hG : 0 < G) (hM : 0 < M) (hSep : IsSeparated G W)
    (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H) :
    (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant M M t u) ≤
      (W.card:ℝ)*atkinsonNearRowBound H G M+∑ t ∈ W, atkinsonFarGapRow H M W t := by
  calc
    _ ≤ ∑ t ∈ W, (atkinsonNearRowBound H G M+atkinsonFarGapRow H M W t) :=
      Finset.sum_le_sum (fun t ht => atkinson_gap_row_le_near_add_far hH hG hM hSep ht hrange)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

def atkinsonSeparatedGapBudget (η H G : ℝ) (N : ℕ) (W : Finset ℝ) : ℝ :=
  (Nat.clog 2 N:ℝ)*∑ j ∈ Finset.range (Nat.clog 2 N),
    (((2^j:ℕ):ℝ)^(1/2+η))*
      ((W.card:ℝ)*atkinsonNearRowBound H G (2^j)+
        ∑ t ∈ W, atkinsonFarGapRow H (2^j) W t)

theorem atkinsonSeparatedGapBudget_empty (η H G : ℝ) (N : ℕ) :
    atkinsonSeparatedGapBudget η H G N ∅ = 0 := by
  simp [atkinsonSeparatedGapBudget]

theorem atkinsonArithmeticGapBudget_le_separated {H G η : ℝ} {N : ℕ} {W : Finset ℝ}
    (hH : 0 < H) (hG : 0 < G) (hSep : IsSeparated G W)
    (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H) :
    atkinsonArithmeticGapBudget η N W ≤ atkinsonSeparatedGapBudget η H G N W := by
  unfold atkinsonArithmeticGapBudget atkinsonSeparatedGapBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left
    (atkinson_gap_double_sum_le_near_add_far hH hG (pow_pos (by norm_num) _) hSep hrange)
    (by positivity)
end MathCollab.Density.Stronger.Atkinson
