module
-- Reversible module-visibility port of the audited development.
/-
Selected finite exponential-overlap/point-mean consumer proofs adapted from
Scott McColm, PointMeanExponentialOverlap.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The repository's literal actual-zeta norm and oneSeparated predicate are used.
-/
public import MathCollab.Density.Stronger.CriticalMoment
public import MathCollab.Density.LargeValueDefinitions
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Normed

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- Exponential decay is bounded by the dyadic geometric weight attached to
the integer shell containing `|u-x|`. -/
theorem exp_neg_abs_le_half_pow_floor (u x : ℝ) :
    Real.exp (-|u - x|) ≤
      (1 / 2 : ℝ) ^ Nat.floor |u - x| := by
  have hfloor : (Nat.floor |u - x| : ℝ) ≤ |u - x| :=
    Nat.floor_le (abs_nonneg _)
  have hexp : Real.exp (-|u - x|) ≤
      Real.exp (-(Nat.floor |u - x| : ℝ)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hfloor)
  have hrewrite : Real.exp (-(Nat.floor |u - x| : ℝ)) =
      (Real.exp (-1)) ^ Nat.floor |u - x| := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    Real.exp (-|u - x|) ≤
        Real.exp (-(Nat.floor |u - x| : ℝ)) := hexp
    _ = (Real.exp (-1)) ^ Nat.floor |u - x| := hrewrite
    _ ≤ (1 / 2 : ℝ) ^ Nat.floor |u - x| :=
      pow_le_pow_left₀ (Real.exp_pos (-1)).le
        Real.exp_neg_one_lt_half.le _

/-- Every distance shell about an arbitrary real centre contains at most two
members of a unit-separated finite set. -/
theorem separated_distance_shell_card_le_two
    (W : Finset ℝ) (x : ℝ) (k : ℕ) (hSep : oneSeparated W) :
    ({u ∈ W | Nat.floor |u - x| = k}).card ≤ 2 := by
  let S := {u ∈ W | Nat.floor |u - x| = k}
  let P : ℝ → Prop := fun u => x ≤ u
  have hpos : (S.filter P).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have haData := Finset.mem_filter.mp ha
    have hbData := Finset.mem_filter.mp hb
    have haS := Finset.mem_filter.mp haData.1
    have hbS := Finset.mem_filter.mp hbData.1
    have haHigh : |a - x| < (k : ℝ) + 1 := by
      rw [← haS.2]
      exact Nat.lt_floor_add_one _
    have hbHigh : |b - x| < (k : ℝ) + 1 := by
      rw [← hbS.2]
      exact Nat.lt_floor_add_one _
    have haLow : (k : ℝ) ≤ |a - x| := by
      rw [← haS.2]
      exact Nat.floor_le (abs_nonneg _)
    have hbLow : (k : ℝ) ≤ |b - x| := by
      rw [← hbS.2]
      exact Nat.floor_le (abs_nonneg _)
    rw [abs_of_nonneg (sub_nonneg.mpr haData.2)] at haHigh haLow
    rw [abs_of_nonneg (sub_nonneg.mpr hbData.2)] at hbHigh hbLow
    have habs : |a - b| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hlarge := hSep a haS.1 b hbS.1 hab
    exact (not_lt_of_ge hlarge) habs
  have hneg : (S.filter (fun u => ¬ P u)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have haData := Finset.mem_filter.mp ha
    have hbData := Finset.mem_filter.mp hb
    have haS := Finset.mem_filter.mp haData.1
    have hbS := Finset.mem_filter.mp hbData.1
    have haHigh : |a - x| < (k : ℝ) + 1 := by
      rw [← haS.2]
      exact Nat.lt_floor_add_one _
    have hbHigh : |b - x| < (k : ℝ) + 1 := by
      rw [← hbS.2]
      exact Nat.lt_floor_add_one _
    have haLow : (k : ℝ) ≤ |a - x| := by
      rw [← haS.2]
      exact Nat.floor_le (abs_nonneg _)
    have hbLow : (k : ℝ) ≤ |b - x| := by
      rw [← hbS.2]
      exact Nat.floor_le (abs_nonneg _)
    have hax : a - x ≤ 0 := by linarith
    have hbx : b - x ≤ 0 := by linarith
    rw [abs_of_nonpos hax] at haHigh haLow
    rw [abs_of_nonpos hbx] at hbHigh hbLow
    have habs : |a - b| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hlarge := hSep a haS.1 b hbS.1 hab
    exact (not_lt_of_ge hlarge) habs
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) P
  change S.card ≤ 2
  omega

/-- The source exponential kernels have a uniform overlap bound. -/
theorem sum_exp_neg_abs_sub_le_four
    (W : Finset ℝ) (x : ℝ) (hSep : oneSeparated W) :
    ∑ u ∈ W, Real.exp (-|u - x|) ≤ 4 := by
  let shell : ℝ → ℕ := fun u => Nat.floor |u - x|
  have hpoint : ∀ u ∈ W, Real.exp (-|u - x|) ≤
      (1 / 2 : ℝ) ^ shell u := by
    intro u _hu
    exact exp_neg_abs_le_half_pow_floor u x
  calc
    ∑ u ∈ W, Real.exp (-|u - x|) ≤
        ∑ u ∈ W, (1 / 2 : ℝ) ^ shell u := by
      exact Finset.sum_le_sum fun u hu => hpoint u hu
    _ = ∑ k ∈ W.image shell,
        ∑ u ∈ W with shell u = k, (1 / 2 : ℝ) ^ shell u := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) _
    _ ≤ ∑ k ∈ W.image shell, 2 * (1 / 2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        ∑ u ∈ W with shell u = k, (1 / 2 : ℝ) ^ shell u =
            (({u ∈ W | shell u = k}).card : ℝ) * (1 / 2 : ℝ) ^ k := by
          rw [Finset.card_eq_sum_ones]
          push_cast
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u hu
          rw [(Finset.mem_filter.mp hu).2]
          simp
        _ ≤ 2 * (1 / 2 : ℝ) ^ k := by
          gcongr
          exact_mod_cast separated_distance_shell_card_le_two W x k hSep
    _ ≤ ∑' k : ℕ, 2 * (1 / 2 : ℝ) ^ k := by
      exact (Summable.mul_left 2 summable_geometric_two).sum_le_tsum _
          (fun k _ => by positivity)
    _ = 4 := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
      · norm_num
      · norm_num

end MathCollab.Density.Stronger.PointMean
