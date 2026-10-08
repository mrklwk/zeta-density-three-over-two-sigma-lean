module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.GammaPhase
public import MathCollab.Density.Stronger.Fourth.GammaShiftAmplitude

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

theorem norm_poleShift_gammaReal_sq_sub_exp_le {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t / 2) :
    ‖zetaSquarePoleShift t w * (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
        Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2 - Complex.exp (w * zetaGammaLeadingLog t)‖ ≤
      (9 * zetaGammaShiftError t w + 12 * ‖w‖ / t) *
        Real.exp (zetaGammaShiftError t w) * Real.exp ((w * zetaGammaLeadingLog t).re) := by
  let R := (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
    Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2
  let E := Complex.exp (w * zetaGammaLeadingLog t)
  have heq : zetaSquarePoleShift t w * R - E =
      zetaSquarePoleShift t w * (R - E) + (zetaSquarePoleShift t w - 1) * E := by ring
  change ‖zetaSquarePoleShift t w * R - E‖ ≤ _
  rw [heq]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hB : 0 ≤ zetaGammaShiftError t w := zetaGammaShiftError_nonneg (by linarith) w
  have hexp : 1 ≤ Real.exp (zetaGammaShiftError t w) := Real.one_le_exp hB
  have hnE : ‖E‖ = Real.exp ((w * zetaGammaLeadingLog t).re) := Complex.norm_exp _
  rw [hnE]
  calc
    _ ≤ 9 * (zetaGammaShiftError t w * Real.exp (zetaGammaShiftError t w) *
        Real.exp ((w * zetaGammaLeadingLog t).re)) +
        (12 * ‖w‖ / t) * Real.exp ((w * zetaGammaLeadingLog t).re) := by
      gcongr
      · exact norm_zetaSquarePoleShift_le (by linarith) hw
      · exact norm_gammaReal_shift_sq_sub_exp_le ht hwre hw
      · exact norm_zetaSquarePoleShift_sub_one_le (by linarith) hw
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ (12 * ‖w‖ / t) * Real.exp ((w * zetaGammaLeadingLog t).re) by positivity)
      nlinarith



def zetaSquareLeadingRightKernel (t u : ℝ) : ℂ :=
  let w : ℂ := 1 + (u : ℂ) * I
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w / w *
    zetaSquareReflectedGammaPhase t * Complex.exp (w * zetaGammaLeadingLog t)

/-- Exact factorization, including the pole amplitude and the source's
Gamma normalization. This is not an independently supplied model kernel. -/
theorem zetaSquareRightKernel_normalized_reflected (t u : ℝ) :
    zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t =
      let w : ℂ := 1 + (u : ℂ) * I
      Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w / w *
        zetaSquareReflectedGammaPhase t * (zetaSquarePoleShift t w *
          (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
            Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2) := by
  dsimp only
  rw [mul_assoc _ (zetaSquareReflectedGammaPhase t),
    mul_comm (zetaSquarePoleShift t _), ← mul_assoc (zetaSquareReflectedGammaPhase t),
    ← zetaSquareGammaNormalization_reflected_factor, zetaSquarePoleShift_eq_source]
  unfold zetaSquareRightKernel
  dsimp only
  rw [zetaSquarePoleNormalization_neg]
  ring

theorem norm_rightContour_shift_le {t u : ℝ} (ht : 4 ≤ t) (hu : |u| ≤ t / 4) :
    ‖(1 : ℂ) + (u : ℂ) * I‖ ≤ t / 2 := by
  have h := norm_add_le (1 : ℂ) ((u : ℂ) * I)
  simp [Real.norm_eq_abs] at h
  linarith

private theorem near_shift_exponent_le {t u : ℝ} (ht : 4 ≤ t) :
    zetaGammaShiftError t (1 + (u : ℂ) * I) + u * (Real.pi / 2) ≤ 20 + 10 * u ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hw : ‖(1 : ℂ) + (u : ℂ) * I‖ ≤ 1 + |u| := by
    simpa [Real.norm_eq_abs] using norm_add_le (1 : ℂ) ((u : ℂ) * I)
  have hB : zetaGammaShiftError t (1 + (u : ℂ) * I) ≤
      (17 * (1 + |u|) + 2 * (1 + |u|) ^ 2) / 4 := by
    unfold zetaGammaShiftError
    gcongr
  have hpi : u * (Real.pi / 2) ≤ 2 * |u| := by
    calc
      _ ≤ |u| * (Real.pi / 2) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ _ := by nlinarith [Real.pi_lt_four, abs_nonneg u]
  nlinarith [sq_abs u, sq_nonneg (|u| - 1)]

/-- The height power in the leading exponential cancels the inverse-height
relative error. The resulting majorant has no height-dependent constant. -/
theorem norm_near_pole_gamma_error_le {t u : ℝ} (ht : 4 ≤ t) (hu : |u| ≤ t / 4) :
    let w : ℂ := 1 + (u : ℂ) * I
    ‖zetaSquarePoleShift t w * (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
        Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2 - Complex.exp (w * zetaGammaLeadingLog t)‖ ≤
      183 * (1 + |u|) ^ 2 * Real.exp (20 + 10 * u ^ 2) := by
  let w : ℂ := 1 + (u : ℂ) * I
  have ht0 : 0 < t := by linarith
  have hwre : 0 ≤ w.re := by norm_num [w]
  have herr := norm_poleShift_gammaReal_sq_sub_exp_le ht hwre (norm_rightContour_shift_le ht hu)
  have he : Real.exp ((w * zetaGammaLeadingLog t).re) =
      t / (2 * Real.pi) * Real.exp (u * (Real.pi / 2)) := by
    rw [zetaGammaLeadingLog_mul_re]
    simp only [w, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      sub_self, add_zero, one_mul, add_im, one_im, mul_im, mul_one, zero_add]
    rw [Real.exp_add, Real.exp_log (by positivity)]
  rw [he] at herr
  have hident : (9 * zetaGammaShiftError t w + 12 * ‖w‖ / t) *
      Real.exp (zetaGammaShiftError t w) * (t / (2 * Real.pi) * Real.exp (u * (Real.pi / 2))) =
      ((165 * ‖w‖ + 18 * ‖w‖ ^ 2) / (2 * Real.pi)) *
        Real.exp (zetaGammaShiftError t w + u * (Real.pi / 2)) := by
    rw [Real.exp_add]
    unfold zetaGammaShiftError
    field_simp
    ring
  rw [hident] at herr
  have hw : ‖w‖ ≤ 1 + |u| := by
    simpa [w, Real.norm_eq_abs] using norm_add_le (1 : ℂ) ((u : ℂ) * I)
  have hpoly : (165 * ‖w‖ + 18 * ‖w‖ ^ 2) / (2 * Real.pi) ≤ 183 * (1 + |u|) ^ 2 := by
    have h1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc
      _ ≤ (165 * (1 + |u|) + 18 * (1 + |u|) ^ 2) / 1 := by gcongr
      _ ≤ _ := by nlinarith [abs_nonneg u]
  exact herr.trans (mul_le_mul hpoly (Real.exp_le_exp.mpr (near_shift_exponent_le ht))
    (Real.exp_pos _).le (by positivity))

/-- The complete normalized source-kernel error has an integrable Gaussian
majorant, uniformly for every height `t ≥ 4` on the stated central segment. -/
theorem norm_zetaSquareRightKernel_sub_leading_near_le {t u : ℝ}
    (ht : 4 ≤ t) (hu : |u| ≤ t / 4) :
    ‖zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t -
      zetaSquareLeadingRightKernel t u‖ ≤
      114375 * Real.exp 120 * Real.exp (-90 * u ^ 2) * (1 + |u|) ^ 10 := by
  let w : ℂ := 1 + (u : ℂ) * I
  let F := Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w / w
  let R := (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
    Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2
  let E := Complex.exp (w * zetaGammaLeadingLog t)
  rw [zetaSquareRightKernel_normalized_reflected]
  change ‖F * zetaSquareReflectedGammaPhase t * (zetaSquarePoleShift t w * R) -
    F * zetaSquareReflectedGammaPhase t * E‖ ≤ _
  rw [← mul_sub, norm_mul, norm_mul, norm_zetaSquareReflectedGammaPhase, mul_one]
  have hw : ‖w‖ ≤ 1 + |u| := by
    simpa [w, Real.norm_eq_abs] using norm_add_le (1 : ℂ) ((u : ℂ) * I)
  have hwlower : 1 ≤ ‖w‖ := by simpa [w] using Complex.abs_re_le_norm w
  have haux := norm_hughesYoungAuxiliaryZero_le_polynomial
    (show 1 ≤ 1 + |u| by linarith [abs_nonneg u]) hw
  have hexp : ‖Complex.exp (100 * w ^ 2)‖ = Real.exp (100 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [w, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hF : ‖F‖ ≤ Real.exp (100 - 100 * u ^ 2) * (625 * (1 + |u|) ^ 8) := by
    dsimp [F]
    rw [norm_div, norm_mul, hexp]
    calc
      _ ≤ (Real.exp (100 - 100 * u ^ 2) * (625 * (1 + |u|) ^ 8)) / 1 := by gcongr
      _ = _ := div_one _
  calc
    _ ≤ (Real.exp (100 - 100 * u ^ 2) * (625 * (1 + |u|) ^ 8)) *
        (183 * (1 + |u|) ^ 2 * Real.exp (20 + 10 * u ^ 2)) :=
      mul_le_mul hF (norm_near_pole_gamma_error_le ht hu) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (100 - 100 * u ^ 2) * Real.exp (20 + 10 * u ^ 2) =
          Real.exp 120 * Real.exp (-90 * u ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = 114375 * (Real.exp (100 - 100 * u ^ 2) * Real.exp (20 + 10 * u ^ 2)) *
            (1 + |u|) ^ 10 := by ring
        _ = _ := by rw [he]; ring

end MathCollab.Density.Stronger.Atkinson
