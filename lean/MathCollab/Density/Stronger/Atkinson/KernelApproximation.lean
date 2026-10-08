module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.NearKernel
public import MathCollab.Density.Stronger.Atkinson.GaussianPolynomial
public import MathCollab.Density.Stronger.Fourth.SquareDivisorSeries

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


def zetaSquareKernelErrorMajorant (u : ℝ) : ℝ :=
  Real.exp (-90 * u ^ 2) * (1 + |u|) ^ 12

theorem zetaSquareKernelErrorMajorant_nonneg (u : ℝ) :
    0 ≤ zetaSquareKernelErrorMajorant u := by unfold zetaSquareKernelErrorMajorant; positivity

theorem integrable_zetaSquareKernelErrorMajorant : Integrable zetaSquareKernelErrorMajorant := by
  change Integrable (fun u : ℝ => Real.exp (-90 * u ^ 2) * (1 + |u|) ^ 12)
  simpa only [zero_sub, neg_mul] using
    (integrable_exp_sub_mul_sq_mul_add_abs_pow 0 (B := 90) (C := 1) (by norm_num) 12)

private theorem gaussian_fusion_le {u b : ℝ} (hb : b ≤ 64 + 10 * u ^ 2) :
    Real.exp (100 - 100 * u ^ 2) * Real.exp b ≤ Real.exp 164 * Real.exp (-90 * u ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith

theorem exists_norm_normalized_zetaSquareRightKernel_far_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t u : ℝ, 4 ≤ t → t / 4 ≤ |u| →
      ‖zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t‖ ≤
        C * zetaSquareKernelErrorMajorant u := by
  obtain ⟨K, hK, hkernel⟩ := exists_zetaSquareRightKernel_uniform_gaussian_bound
  obtain ⟨D, hD, hden⟩ := exists_norm_inv_zetaSquareGammaNormalization_le
  refine ⟨K * D * 5 ^ 12 * Real.exp 164, by positivity, ?_⟩
  intro t u ht hu
  have ht0 : 0 ≤ t := by linarith
  have hpoly : 3 + |t| + |u| ≤ 5 * (1 + |u|) := by rw [abs_of_nonneg ht0]; linarith
  have he : Real.pi * t ≤ 64 + 10 * u ^ 2 := by
    have hpi : Real.pi * t ≤ 4 * t := mul_le_mul_of_nonneg_right Real.pi_lt_four.le ht0
    nlinarith [sq_nonneg (|u| - 8), sq_abs u]
  have hd := hden t
  rw [abs_of_nonneg ht0] at hd
  have hk := hkernel (-t) u
  rw [abs_neg] at hk
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (K * Real.exp (100 - 100 * u ^ 2) * (5 * (1 + |u|)) ^ 12) *
        (D * Real.exp (Real.pi * t)) := by
      gcongr
      exact hk.trans (by gcongr)
    _ = (K * D * 5 ^ 12) * (Real.exp (100 - 100 * u ^ 2) * Real.exp (Real.pi * t)) *
        (1 + |u|) ^ 12 := by ring
    _ ≤ (K * D * 5 ^ 12) * (Real.exp 164 * Real.exp (-90 * u ^ 2)) * (1 + |u|) ^ 12 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (gaussian_fusion_le he) (by positivity)) (by positivity)
    _ = _ := by unfold zetaSquareKernelErrorMajorant; ring

theorem continuous_zetaSquareLeadingRightKernel (t : ℝ) :
    Continuous (zetaSquareLeadingRightKernel t) := by
  have haux := differentiable_hughesYoungAuxiliaryZero.continuous
  have hw : ∀ u : ℝ, (1 : ℂ) + (u : ℂ) * I ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    norm_num at this
  unfold zetaSquareLeadingRightKernel
  dsimp only
  fun_prop (disch := aesop)

theorem norm_zetaSquareLeadingRightKernel {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ‖zetaSquareLeadingRightKernel t u‖ =
      Real.exp (100 - 100 * u ^ 2) * ‖hughesYoungAuxiliaryZero (1 + (u : ℂ) * I)‖ /
        ‖(1 : ℂ) + (u : ℂ) * I‖ * (t / (2 * Real.pi) * Real.exp (u * (Real.pi / 2))) := by
  unfold zetaSquareLeadingRightKernel
  dsimp only
  rw [norm_mul, norm_mul, norm_zetaSquareReflectedGammaPhase, mul_one,
    norm_div, norm_mul, Complex.norm_exp, Complex.norm_exp, zetaGammaLeadingLog_mul_re]
  have he : (100 * ((1 : ℂ) + (u : ℂ) * I) ^ 2).re = 100 - 100 * u ^ 2 := by
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [he]
  simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    sub_self, add_zero, one_mul, add_im, one_im, mul_im, mul_one, zero_add]
  rw [Real.exp_add, Real.exp_log (by positivity)]

theorem exists_norm_zetaSquareLeadingRightKernel_far_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t u : ℝ, 4 ≤ t → t / 4 ≤ |u| →
      ‖zetaSquareLeadingRightKernel t u‖ ≤ C * zetaSquareKernelErrorMajorant u := by
  refine ⟨2500 * Real.exp 164, by positivity, ?_⟩
  intro t u ht hu
  have ht0 : 0 < t := by linarith
  let R : ℝ := 1 + |u|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg u]
  have hw : ‖(1 : ℂ) + (u : ℂ) * I‖ ≤ R := by
    simpa [R, Real.norm_eq_abs] using norm_add_le (1 : ℂ) ((u : ℂ) * I)
  have hwlower : 1 ≤ ‖(1 : ℂ) + (u : ℂ) * I‖ := by
    simpa using Complex.abs_re_le_norm ((1 : ℂ) + (u : ℂ) * I)
  have haux := norm_hughesYoungAuxiliaryZero_le_polynomial hR hw
  have htR : t / (2 * Real.pi) ≤ 4 * R := by
    calc
      _ ≤ t / 1 := by gcongr; linarith [Real.pi_gt_three]
      _ ≤ _ := by dsimp [R]; linarith
  have he : u * (Real.pi / 2) ≤ 64 + 10 * u ^ 2 := by
    have h : u * (Real.pi / 2) ≤ 2 * |u| := by
      apply (mul_le_mul_of_nonneg_right (le_abs_self u) (by positivity : 0 ≤ Real.pi / 2)).trans
      nlinarith [Real.pi_lt_four, abs_nonneg u]
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  rw [norm_zetaSquareLeadingRightKernel ht0]
  calc
    _ ≤ Real.exp (100 - 100 * u ^ 2) * (625 * R ^ 8) / 1 *
        (4 * R * Real.exp (u * (Real.pi / 2))) := by gcongr
    _ = 2500 * (Real.exp (100 - 100 * u ^ 2) * Real.exp (u * (Real.pi / 2))) * R ^ 9 := by ring
    _ ≤ 2500 * (Real.exp 164 * Real.exp (-90 * u ^ 2)) * R ^ 12 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (gaussian_fusion_le he) (by norm_num))
        (pow_le_pow_right₀ hR (show (9 : ℕ) ≤ 12 by norm_num)) (by positivity) (by positivity)
    _ = _ := by unfold zetaSquareKernelErrorMajorant; dsimp [R]; ring

/-- A single integrable error majorant for the complete reflected source
kernel. Near and far estimates are both actually consumed by this theorem. -/
theorem exists_norm_zetaSquareRightKernel_sub_leading_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t u : ℝ, 4 ≤ t →
      ‖zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t -
        zetaSquareLeadingRightKernel t u‖ ≤ C * zetaSquareKernelErrorMajorant u := by
  obtain ⟨K, hK, hk⟩ := exists_norm_normalized_zetaSquareRightKernel_far_le
  obtain ⟨L, hL, hl⟩ := exists_norm_zetaSquareLeadingRightKernel_far_le
  let N : ℝ := 114375 * Real.exp 120
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨N + K + L, by positivity, ?_⟩
  intro t u ht
  have hm := zetaSquareKernelErrorMajorant_nonneg u
  by_cases hu : |u| ≤ t / 4
  · apply (norm_zetaSquareRightKernel_sub_leading_near_le ht hu).trans
    calc
      _ ≤ N * zetaSquareKernelErrorMajorant u := by
        unfold zetaSquareKernelErrorMajorant
        dsimp [N]
        have hp := pow_le_pow_right₀ (show 1 ≤ 1 + |u| by linarith [abs_nonneg u])
          (show (10 : ℕ) ≤ 12 by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left hp
          (show 0 ≤ 114375 * Real.exp 120 * Real.exp (-90 * u ^ 2) by positivity)]
      _ ≤ _ := by nlinarith
  · apply (norm_sub_le _ _).trans
    apply (add_le_add (hk t u ht (le_of_not_ge hu)) (hl t u ht (le_of_not_ge hu))).trans
    nlinarith

theorem integrable_zetaSquareRightKernel_error {t : ℝ} (ht : 4 ≤ t) :
    Integrable (fun u : ℝ => zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t -
      zetaSquareLeadingRightKernel t u) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_zetaSquareRightKernel_sub_leading_le
  apply (integrable_zetaSquareKernelErrorMajorant.const_mul C).mono'
    (((continuous_zetaSquareRightKernel (-t)).div_const _).sub
      (continuous_zetaSquareLeadingRightKernel t)).aestronglyMeasurable
  filter_upwards with u
  exact hbound t u ht

theorem integrable_zetaSquareLeadingRightKernel {t : ℝ} (ht : 4 ≤ t) :
    Integrable (zetaSquareLeadingRightKernel t) := by
  have h := ((integrable_zetaSquareRightKernel (-t)).div_const
    (zetaSquareGammaNormalization t)).sub (integrable_zetaSquareRightKernel_error ht)
  convert h using 1
  funext u
  simp only [Pi.sub_apply, sub_sub_cancel]

/-- The whole-line integrated absolute error has one uniform constant.
This supplies an honest `O(1)` kernel remainder before the divisor series
is opened or any local-height average is taken. -/
theorem exists_integral_norm_zetaSquareRightKernel_error_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ t →
      (∫ u : ℝ, ‖zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t -
        zetaSquareLeadingRightKernel t u‖) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSquareRightKernel_sub_leading_le
  have hm : 0 ≤ ∫ u : ℝ, zetaSquareKernelErrorMajorant u :=
    integral_nonneg zetaSquareKernelErrorMajorant_nonneg
  refine ⟨1 + C * ∫ u : ℝ, zetaSquareKernelErrorMajorant u, by positivity, ?_⟩
  intro t ht
  have h := integral_mono (integrable_zetaSquareRightKernel_error ht).norm
    (integrable_zetaSquareKernelErrorMajorant.const_mul C) (fun u => hbound t u ht)
  rw [integral_const_mul] at h
  linarith

end MathCollab.Density.Stronger.Atkinson
