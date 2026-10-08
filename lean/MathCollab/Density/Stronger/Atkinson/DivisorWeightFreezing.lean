module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightMass

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


def zetaSquareFrozenDivisorContribution (T x : ℝ) (n : ℕ) : ℂ :=
  divisorDirichletTerm (afeCriticalPoint (-(T + x))) n * zetaSquareReflectedGammaPhase (T + x) *
    zetaDivisorWeight (zetaDivisorWeightArgument T n)

def zetaSquareFrozenDivisorIntegral (T x : ℝ) : ℂ :=
  ∑' n : ℕ, zetaSquareFrozenDivisorContribution T x n

theorem summable_zetaSquareFrozenDivisorContribution {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Summable (zetaSquareFrozenDivisorContribution T x) := by
  apply summable_norm_iff.mp
  have h := summable_norm_source_divisor_weight hT (-(T + x))
  simpa only [zetaSquareFrozenDivisorContribution, norm_mul,
    norm_zetaSquareReflectedGammaPhase, mul_one] using h

theorem norm_zetaSquareDivisor_freezing_error (T x : ℝ) (n : ℕ) :
    ‖zetaSquareLeadingDivisorContribution (T + x) n - zetaSquareFrozenDivisorContribution T x n‖ =
      ‖divisorDirichletTerm (afeCriticalPoint (-(T + x))) n‖ *
        ‖zetaDivisorWeight (zetaDivisorWeightArgument (T + x) n) -
          zetaDivisorWeight (zetaDivisorWeightArgument T n)‖ := by
  rw [zetaSquareLeadingDivisorContribution_eq_weight]
  unfold zetaSquareFrozenDivisorContribution
  rw [← mul_sub, norm_mul, norm_mul, norm_zetaSquareReflectedGammaPhase, mul_one]

theorem min_self_inv_le_min_one (a : ℝ) : min a a⁻¹ ≤ min 1 a := by
  by_cases ha : a ≤ 1
  · rw [min_eq_right ha]
    exact min_le_left _ _
  · rw [min_eq_left (le_of_not_ge ha)]
    apply (min_le_right _ _).trans
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one (le_of_not_ge ha)

theorem exists_norm_zetaSquareDivisor_freezing_error_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ, |x| ≤ T / 2 → ∀ n : ℕ,
      ‖zetaSquareLeadingDivisorContribution (T + x) n - zetaSquareFrozenDivisorContribution T x n‖ ≤
        (C * (|x| / T)) * (‖divisorDirichletTerm (afeCriticalPoint (-(T + x))) n‖ *
          min 1 (T / (2 * Real.pi * (n : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_source_zetaDivisorWeight_height_sub_le
  refine ⟨C, hC, ?_⟩
  intro T hT x hx n
  rw [norm_zetaSquareDivisor_freezing_error]
  by_cases hn : n = 0
  · simp [hn, divisorDirichletTerm, LSeries.term]
  have hm : min (T / (2 * Real.pi * (n : ℝ))) ((2 * Real.pi * (n : ℝ)) / T) ≤
      min 1 (T / (2 * Real.pi * (n : ℝ))) := by
    simpa only [inv_div] using min_self_inv_le_min_one (T / (2 * Real.pi * (n : ℝ)))
  calc
    _ ≤ ‖divisorDirichletTerm (afeCriticalPoint (-(T + x))) n‖ *
        (C * (|x| / T) * min (T / (2 * Real.pi * (n : ℝ))) ((2 * Real.pi * (n : ℝ)) / T)) :=
      mul_le_mul_of_nonneg_left (hbound T hT x hx n (Nat.pos_of_ne_zero hn)) (norm_nonneg _)
    _ ≤ ‖divisorDirichletTerm (afeCriticalPoint (-(T + x))) n‖ *
        (C * (|x| / T) * min 1 (T / (2 * Real.pi * (n : ℝ)))) := by gcongr
    _ = _ := by ring

/-- The complete leading source is approximated by its frozen-weight
series. The phase and Dirichlet oscillation are still at `T+x`, and the
error has the inverse square-root height gain needed for local averaging. -/
theorem exists_norm_zetaSquareLeadingDivisor_sub_frozen_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 8 ≤ T → ∀ x : ℝ, |x| ≤ T / 2 →
      ‖zetaSquareLeadingDivisorIntegral (T + x) - zetaSquareFrozenDivisorIntegral T x‖ ≤
        C * |x| * T ^ (-1 / 2 + ε) := by
  obtain ⟨C, hC, hpoint⟩ := exists_norm_zetaSquareDivisor_freezing_error_le
  obtain ⟨D, hD, hmass⟩ := exists_tsum_divisorCritical_min_height_le ε hε
  refine ⟨C * D, by positivity, ?_⟩
  intro T hT x hx
  have hT0 : 0 < T := by linarith
  have hTx : 4 ≤ T + x := by have := neg_abs_le x; linarith
  let e := fun n : ℕ => zetaSquareLeadingDivisorContribution (T + x) n -
    zetaSquareFrozenDivisorContribution T x n
  let m := fun n : ℕ => ‖divisorDirichletTerm (afeCriticalPoint (-(T + x))) n‖ *
    min 1 (T / (2 * Real.pi * (n : ℝ)))
  have hsum : HasSum e (zetaSquareLeadingDivisorIntegral (T + x) - zetaSquareFrozenDivisorIntegral T x) :=
    (hasSum_zetaSquareLeadingDivisorContribution hTx).sub
      (summable_zetaSquareFrozenDivisorContribution hT0 x).hasSum
  have hm : Summable m := by
    simpa only [div_div] using summable_divisorCritical_min (A := T / (2 * Real.pi))
      (θ := 3 / 4) (by positivity) (by norm_num) (by norm_num) (-(T + x))
  have he : Summable (fun n => ‖e n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (hpoint T hT0 x hx)
      (hm.mul_left (C * (|x| / T)))
  rw [← hsum.tsum_eq]
  calc
    _ ≤ ∑' n : ℕ, ‖e n‖ := norm_tsum_le_tsum_norm he
    _ ≤ ∑' n : ℕ, (C * (|x| / T)) * m n :=
      Summable.tsum_le_tsum (hpoint T hT0 x hx) he (hm.mul_left _)
    _ = (C * (|x| / T)) * ∑' n : ℕ, m n := tsum_mul_left
    _ ≤ (C * (|x| / T)) * (D * T ^ (1 / 2 + ε)) := by
      apply mul_le_mul_of_nonneg_left (hmass T (by linarith) (-(T + x))) (by positivity)
    _ = _ := by
      have hp : T ^ (1 / 2 + ε) = T ^ (-1 / 2 + ε) * T := by
        calc
          _ = T ^ ((-1 / 2 + ε) + 1) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hT0, Real.rpow_one]
      rw [hp]
      field_simp

/-- The preceding weight freeze also consumes the already proved actual
reflected source remainder. This is still a complete series, not yet a
shortened Atkinson sum. -/
theorem exists_norm_zetaSquareSource_sub_frozen_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 8 ≤ T → ∀ x : ℝ, |x| ≤ T / 2 →
      ‖zetaSquareDivisorIntegral (-(T + x)) / zetaSquareGammaNormalization (T + x) -
        zetaSquareFrozenDivisorIntegral T x‖ ≤ C * (1 + |x| * T ^ (-1 / 2 + ε)) := by
  obtain ⟨C, hC, hsource⟩ := exists_norm_zetaSquareDivisorIntegral_sub_leading_le
  obtain ⟨D, hD, hfreeze⟩ := exists_norm_zetaSquareLeadingDivisor_sub_frozen_le ε hε
  refine ⟨C + D, by positivity, ?_⟩
  intro T hT x hx
  have hTx : 4 ≤ T + x := by have := neg_abs_le x; linarith
  apply (norm_sub_le_norm_sub_add_norm_sub _ (zetaSquareLeadingDivisorIntegral (T + x)) _).trans
  apply (add_le_add (hsource (T + x) hTx) (hfreeze T hT x hx)).trans
  nlinarith [mul_nonneg (abs_nonneg x) (Real.rpow_nonneg (by linarith : 0 ≤ T) (-1 / 2 + ε))]

end MathCollab.Density.Stronger.Atkinson
