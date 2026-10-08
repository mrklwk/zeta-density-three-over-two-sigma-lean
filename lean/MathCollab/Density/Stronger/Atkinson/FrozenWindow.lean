module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.FrozenDivisorGaussian
public import MathCollab.Density.Stronger.Atkinson.RealFrozenSource
public import MathCollab.Density.Stronger.Atkinson.GaussianZetaTail

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


theorem norm_zetaSquareFrozenDivisorContribution (T x : ℝ) (n : ℕ) :
    ‖zetaSquareFrozenDivisorContribution T x n‖ = ‖zetaFrozenDivisorCoefficient T n‖ := by
  rw [zetaSquareFrozenDivisorContribution_eq_phase, norm_mul, norm_mul,
    norm_zetaSquareReflectedGammaPhase]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    mul_one, one_mul, Real.exp_zero]

theorem continuous_zetaSquareFrozenDivisorIntegral {T : ℝ} (hT : 0 < T) :
    Continuous (zetaSquareFrozenDivisorIntegral T) := by
  apply continuous_tsum (u := fun n => ‖zetaFrozenDivisorCoefficient T n‖)
  · intro n
    simp_rw [zetaSquareFrozenDivisorContribution_eq_phase]
    have hc : Continuous zetaSquareReflectedGammaPhase :=
      continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_zetaSquareReflectedGammaPhase t).continuousAt)
    fun_prop (disch := assumption)
  · exact summable_norm_zetaFrozenDivisorCoefficient hT
  · intro n x
    exact (norm_zetaSquareFrozenDivisorContribution T x n).le

theorem norm_zetaSquareFrozenDivisorIntegral_le_mass {T : ℝ} (hT : 0 < T) (x : ℝ) :
    ‖zetaSquareFrozenDivisorIntegral T x‖ ≤ ∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖ := by
  have h := norm_tsum_le_tsum_norm (summable_zetaSquareFrozenDivisorContribution hT x).norm
  simpa only [norm_zetaSquareFrozenDivisorContribution, zetaSquareFrozenDivisorIntegral] using h

theorem integrable_zetaSquareFrozenDivisor_gaussian {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0) :
    Integrable (fun x : ℝ => zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)) := by
  have hc : Continuous (fun x : ℝ => zetaSquareFrozenDivisorIntegral T x *
      (Real.exp (-(x / G) ^ 2) : ℂ)) :=
    (continuous_zetaSquareFrozenDivisorIntegral hT).mul (by fun_prop)
  apply ((integrable_physical_gaussian hG).const_mul
    (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖)).mono' hc.aestronglyMeasurable
  filter_upwards with x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (norm_zetaSquareFrozenDivisorIntegral_le_mass hT x) (Real.exp_pos _).le

theorem norm_zetaFrozenDivisorGaussianMean_sub_window_le {T G r : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hr : 0 ≤ r) :
    ‖zetaFrozenDivisorGaussianMean T G - ∫ x in -r..r,
      zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)‖ ≤
      (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
        (Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2)) := by
  have hf := integrable_zetaSquareFrozenDivisor_gaussian hT hG.ne'
  rw [zetaFrozenDivisorGaussianMean, intervalIntegral.integral_of_le (by linarith),
    ← setIntegral_compl measurableSet_Ioc hf]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x in (Ioc (-r) r)ᶜ, (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
        Real.exp (-(x / G) ^ 2) := by
      apply integral_mono_ae hf.norm.integrableOn ((integrable_physical_gaussian hG.ne').const_mul _).integrableOn
      filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (norm_zetaSquareFrozenDivisorIntegral_le_mass hT x) (Real.exp_pos _).le
    _ = (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
        ∫ x in (Ioc (-r) r)ᶜ, Real.exp (-(x / G) ^ 2) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (physical_gaussian_tail_le hG hr) (tsum_nonneg (fun _ => norm_nonneg _))

theorem zetaSquareGaussianWindow_eq_height_shift (T r : ℝ) {G : ℝ} (hG : G ≠ 0) :
    zetaSquareGaussianWindow T G (r / G) =
      ∫ x in -r..r, Real.exp (-(x / G) ^ 2) * zetaMomentCriticalNorm (T + x) ^ 2 := by
  have h := intervalIntegral.integral_comp_add_left
    (fun t => zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2)
    (a := -r) (b := r) T
  simpa only [zetaSquareGaussianWindow, zetaGaussianWeight, add_sub_cancel_left,
    mul_div_cancel₀ _ hG, ← sub_eq_add_neg] using h.symm

/-- Finite-window source remainder after actual Gaussian weighting. -/
theorem exists_abs_zetaSquareGaussianWindow_sub_frozen_window_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G r : ℝ, 8 ≤ T → 0 < G → 0 ≤ r → r ≤ T / 2 →
      |zetaSquareGaussianWindow T G (r / G) - 2 *
        (∫ x in -r..r, zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)).re| ≤
        C * r * (1 + r * T ^ (-1 / 2 + ε)) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_zetaSquareNorm_sub_frozen_le ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro T G r hT hG hr hrT
  have hT0 : 0 < T := by linarith
  let F : ℝ → ℝ := fun x => Real.exp (-(x / G) ^ 2) *
    (zetaMomentCriticalNorm (T + x) ^ 2 - 2 * (zetaSquareFrozenDivisorIntegral T x).re)
  have hz : Continuous (fun x : ℝ => Real.exp (-(x / G) ^ 2) * zetaMomentCriticalNorm (T + x) ^ 2) := by
    have hc := continuous_zetaMomentCriticalNorm
    fun_prop (disch := assumption)
  have hf : Continuous (fun x : ℝ => zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)) :=
    (continuous_zetaSquareFrozenDivisorIntegral hT0).mul (by fun_prop)
  have hre : (∫ x in -r..r, zetaSquareFrozenDivisorIntegral T x *
      (Real.exp (-(x / G) ^ 2) : ℂ)).re =
      ∫ x in -r..r, (zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)).re := by
    simp only [intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    exact (integral_re (hf.intervalIntegrable (-r) r).1).symm
  have hfi : IntervalIntegrable (fun x : ℝ => 2 *
      (zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)).re) volume (-r) r := by
    simpa only [Function.comp_apply] using
      (((Complex.continuous_re.comp hf).intervalIntegrable (-r) r).const_mul 2)
  have heq : zetaSquareGaussianWindow T G (r / G) - 2 *
      (∫ x in -r..r, zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)).re =
      ∫ x in -r..r, F x := by
    rw [zetaSquareGaussianWindow_eq_height_shift T r hG.ne',
      hre, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hz.intervalIntegrable (-r) r) hfi]
    congr 1
    funext x
    dsimp only [F]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [heq, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -r) (b := r) (C := C * (1 + r * T ^ (-1 / 2 + ε))) (f := F) (by
      intro x hx
      have hxabs : |x| ≤ r := by
        rw [uIoc_of_le (by linarith)] at hx
        exact abs_le.mpr ⟨hx.1.le, hx.2⟩
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ 1 * (C * (1 + |x| * T ^ (-1 / 2 + ε))) :=
          mul_le_mul (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x / G)]))
            (hbound T hT x (hxabs.trans hrT)) (abs_nonneg _) (by norm_num)
        _ ≤ C * (1 + r * T ^ (-1 / 2 + ε)) := by simp only [one_mul]; gcongr)
  apply h.trans_eq
  rw [abs_of_nonneg (by linarith : 0 ≤ r - -r)]
  ring

/-- The actual local zeta Gaussian window is now linked to the complete
quadratic divisor sum. The three errors are the actual source freeze,
the two frozen Gaussian tails and the actual Gamma-phase replacement.
Divisor shortening and arithmetic cancellation are not asserted here. -/
theorem exists_abs_zetaSquareGaussianWindow_sub_quadratic_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G r : ℝ, 8 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 ≤ r → r ≤ T / 2 →
      |zetaSquareGaussianWindow T G (r / G) - 2 * (zetaFrozenDivisorQuadraticSum T G).re| ≤
        C * r * (1 + r * T ^ (-1 / 2 + ε)) +
          (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
            (4 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
              6 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_zetaSquareGaussianWindow_sub_frozen_window_le ε hε
  refine ⟨C, hC, ?_⟩
  intro T G r hT hG hGT hr hrT
  let F : ℂ := ∫ x in -r..r, zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)
  have hfinite := hbound T G r hT hG hr hrT
  change |zetaSquareGaussianWindow T G (r / G) - 2 * F.re| ≤ _ at hfinite
  have htail := norm_zetaFrozenDivisorGaussianMean_sub_window_le (by linarith : 0 < T) hG hr
  have hphase := norm_zetaFrozenDivisorGaussianMean_sub_quadratic_le (by linarith : 4 ≤ T) hG hGT hr hrT
  have htri := norm_sub_le_norm_sub_add_norm_sub F (zetaFrozenDivisorGaussianMean T G)
    (zetaFrozenDivisorQuadraticSum T G)
  have hre : |2 * F.re - 2 * (zetaFrozenDivisorQuadraticSum T G).re| ≤
      2 * ‖F - zetaFrozenDivisorQuadraticSum T G‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (F - zetaFrozenDivisorQuadraticSum T G))
      (by norm_num)
  have hreal := abs_sub_le (zetaSquareGaussianWindow T G (r / G)) (2 * F.re)
    (2 * (zetaFrozenDivisorQuadraticSum T G).re)
  change ‖zetaFrozenDivisorGaussianMean T G - F‖ ≤ _ at htail
  rw [norm_sub_rev] at htail
  nlinarith

end MathCollab.Density.Stronger.Atkinson
