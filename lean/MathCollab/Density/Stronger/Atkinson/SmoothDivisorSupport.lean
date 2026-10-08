module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorTest

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem zetaDivisorBandEdge_outer_bounds {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 ≤ L) (hwidth : 8 * L ≤ G) :
    T / (4 * Real.pi) ≤ zetaDivisorBandEdge T G (-2 * L) ∧
      zetaDivisorBandEdge T G (2 * L) ≤ T / Real.pi := by
  have hr0 : 0 ≤ 2 * L / G := by positivity
  have hr : 2 * L / G ≤ 1 / 4 := by
    apply (div_le_iff₀ hG).mpr
    linarith
  have hlo := Real.add_one_le_exp (-(2 * L / G))
  have hhi := exp_sub_one_le_two_mul hr0 (by linarith : 2 * L / G ≤ 1)
  have hA : 0 < T / (2 * Real.pi) := by positivity
  have hl := mul_le_mul_of_nonneg_left hlo hA.le
  have hu := mul_le_mul_of_nonneg_left hhi hA.le
  unfold zetaDivisorBandEdge
  rw [show -2 * L / G = -(2 * L / G) by ring]
  have hhalfeq : T / (4 * Real.pi) = (T / (2 * Real.pi)) / 2 := by ring
  have hdouble : T / Real.pi = 2 * (T / (2 * Real.pi)) := by ring
  rw [hhalfeq, hdouble]
  constructor <;> nlinarith

theorem support_zetaSmoothDivisorTest_physical {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Function.support (zetaSmoothDivisorTest T G L) ⊆ Icc (T / 16) T := by
  intro x hx
  have hs := support_zetaSmoothDivisorTest hT hG hL hx
  have hb := zetaDivisorBandEdge_outer_bounds hT hG hL.le hwidth
  have hlow : T / 16 ≤ T / (4 * Real.pi) := by
    exact div_le_div_of_nonneg_left hT.le (by positivity)
      (by nlinarith [Real.pi_lt_four])
  have hhigh : T / Real.pi ≤ T := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  exact ⟨hlow.trans (hb.1.trans hs.1), (hs.2.trans hb.2).trans hhigh⟩

theorem eventually_zetaSmoothDivisorTest_support_physical {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, 16 ≤ T ∧ ∀ G : ℝ, T ^ δ ≤ G →
      0 < G ∧ 0 < Real.log T ∧ 8 * Real.log T ≤ G ∧
        Function.support (zetaSmoothDivisorTest T G (Real.log T)) ⊆ Icc (T / 16) T := by
  filter_upwards [eventually_const_log_pow_le_rpow 8 (by norm_num) 1 hδ,
    eventually_ge_atTop (16 : ℝ)] with T hlog hT
  refine ⟨hT, ?_⟩
  intro G hG
  have hT0 : 0 < T := by linarith
  have hG0 : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hG
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hwidth : 8 * Real.log T ≤ G := by simpa only [pow_one] using hlog.trans hG
  exact ⟨hG0, hlog0, hwidth, support_zetaSmoothDivisorTest_physical hT0 hG0 hlog0 hwidth⟩

end MathCollab.Density.Stronger.Atkinson
