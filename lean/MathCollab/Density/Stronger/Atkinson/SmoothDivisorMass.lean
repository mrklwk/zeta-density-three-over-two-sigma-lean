module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport

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


theorem exists_norm_zetaShortDivisorTestFunction_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G x : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T → 1 ≤ x →
      ‖zetaShortDivisorTestFunction T G x‖ ≤ C * G := by
  obtain ⟨C, hC, hweight⟩ := exists_norm_zetaDivisorWeight_min_le
    (B := Real.pi / 2) (by positivity)
  refine ⟨C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G x hT hG hGT hx
  have hx0 : 0 < x := by linarith
  have harg : |((Real.log x : ℂ) - zetaGammaLeadingLog T).im| ≤ Real.pi / 2 := by
    simp only [zetaGammaLeadingLog, Complex.sub_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, add_zero, zero_sub, neg_neg, abs_of_pos (by positivity : 0 < Real.pi / 2)]
    rfl
  have hw := (hweight ((Real.log x : ℂ) - zetaGammaLeadingLog T) harg).trans
    (mul_le_of_le_one_right hC.le (min_le_left _ _))
  have hp : ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + (T : ℂ) * I)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (((-1 / 2 : ℂ) + (T : ℂ) * I)).re = -(1 / 2 : ℝ) := by norm_num
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  unfold zetaShortDivisorTestFunction
  rw [norm_mul, norm_mul, norm_mul, norm_zetaSquareReflectedGammaPhase, mul_one]
  calc
    _ ≤ 1 * C * (Real.sqrt Real.pi * G) := by
      exact mul_le_mul (mul_le_mul hp hw (norm_nonneg _) (by norm_num))
        (norm_zetaGaussianQuadraticIntegral_le_mass hT hG hGT _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem exists_norm_zetaSmoothDivisorTest_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ x : ℝ, ‖zetaSmoothDivisorTest T G L x‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaShortDivisorTestFunction_le
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth x
  by_cases hx : zetaSmoothDivisorTest T G L x = 0
  · rw [hx, norm_zero]
    positivity
  have hs := support_zetaSmoothDivisorTest_physical (by linarith : 0 < T) hG hL hwidth hx
  have hx1 : 1 ≤ x := by linarith [hs.1]
  unfold zetaSmoothDivisorTest
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, zetaDivisorBandCutoff,
    abs_of_nonneg (zetaBandCutoff_nonneg _ _ _ _ _)]
  apply (mul_le_of_le_one_left (norm_nonneg _) (zetaBandCutoff_le_one _ _ _ _ _)).trans
  exact hbound T G x (by linarith) hG hGT hx1

theorem integrable_zetaSmoothDivisorTest {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) : Integrable (zetaSmoothDivisorTest T G L) := by
  let hg := zetaSmoothDivisorVoronoiTest hT hG hL
  exact hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport

theorem zetaSmoothDivisorTest_integral_norm_eq_physical {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    (∫ x : ℝ in Ioi 0, ‖zetaSmoothDivisorTest T G L x‖) =
      ∫ x : ℝ in Icc (T / 16) T, ‖zetaSmoothDivisorTest T G L x‖ := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun x hx => (by positivity : 0 < T / 16).trans_le hx.1)
  intro x hx
  have hzero : zetaSmoothDivisorTest T G L x = 0 := by
    by_contra hn
    exact hx.2 (support_zetaSmoothDivisorTest_physical hT hG hL hwidth hn)
  simp only [hzero, norm_zero]

theorem exists_integral_norm_zetaSmoothDivisorTest_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
      (∫ x : ℝ in Ioi 0, ‖zetaSmoothDivisorTest T G L x‖) ≤ C * G * T := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSmoothDivisorTest_le
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  rw [zetaSmoothDivisorTest_integral_norm_eq_physical (by linarith) hG hL hwidth]
  have hi := norm_setIntegral_le_of_norm_le_const
    (s := Icc (T / 16) T)
    (f := fun x => ‖zetaSmoothDivisorTest T G L x‖) (isCompact_Icc.measure_lt_top (μ := volume))
    (fun x _ => by simpa only [norm_norm] using hbound T G L hT hG hGT hL hwidth x)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
    Real.volume_real_Icc_of_le (by linarith : T / 16 ≤ T)] at hi
  apply hi.trans
  nlinarith [mul_pos hC hG]

end MathCollab.Density.Stronger.Atkinson
