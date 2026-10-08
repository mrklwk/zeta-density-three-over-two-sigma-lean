module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.QuadraticGaussian
public import Mathlib

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Second derivative of the actual quadratic Gaussian

The exact differentiated transform and its damping remain visible.
The inverse quadratic coefficient is bounded by the real Gaussian
width; no estimate for a substitute amplitude is assumed.
-/

noncomputable section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

theorem hasDerivAt_deriv_zetaGaussianQuadraticIntegral (T : ℝ) {G : ℝ}
    (hG : G ≠ 0) (v : ℝ) :
    HasDerivAt (deriv (zetaGaussianQuadraticIntegral T G))
      ((((v : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G ^ 2)) -
        1 / (2 * zetaGaussianQuadraticCoefficient T G)) *
          zetaGaussianQuadraticIntegral T G v) v := by
  have he : deriv (zetaGaussianQuadraticIntegral T G) = fun w : ℝ =>
      -(w : ℂ) / (2 * zetaGaussianQuadraticCoefficient T G) *
        zetaGaussianQuadraticIntegral T G w :=
    funext (fun w => (hasDerivAt_zetaGaussianQuadraticIntegral T hG w).deriv)
  have h := (((hasDerivAt_id v).ofReal_comp.neg).div_const
    (2 * zetaGaussianQuadraticCoefficient T G)).mul
      (hasDerivAt_zetaGaussianQuadraticIntegral T hG v)
  rw [he]
  convert h using 1
  · rfl
  · simp only [Complex.ofReal_one, Pi.neg_apply, id_eq]
    ring

theorem norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖iteratedDeriv 2 (zetaGaussianQuadraticIntegral T G) v‖ ≤
      (v ^ 2 * G ^ 4 / 4 + G ^ 2 / 2) *
        (Real.sqrt Real.pi * G * Real.exp (-(G * v) ^ 2 / 8)) := by
  have hcoef := inverse_norm_zetaGaussianQuadraticCoefficient_le T hG.ne'
  have hcoef0 : 0 ≤ 1 / ‖zetaGaussianQuadraticCoefficient T G‖ := by positivity
  have hsq := pow_le_pow_left₀ hcoef0 hcoef 2
  have hp : ‖(v : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G ^ 2) -
      1 / (2 * zetaGaussianQuadraticCoefficient T G)‖ ≤
      v ^ 2 * G ^ 4 / 4 + G ^ 2 / 2 := by
    apply (norm_sub_le _ _).trans
    simp only [norm_div, norm_mul, norm_pow, norm_one, norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ v ^ 2 / 4 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcoef (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert add_le_add h1 h2 using 1 <;> ring
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    (hasDerivAt_deriv_zetaGaussianQuadraticIntegral T hG.ne' v).deriv, norm_mul]
  exact mul_le_mul hp (norm_zetaGaussianQuadraticIntegral_le hT hG hGT v)
    (norm_nonneg _) (by positivity)

theorem norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le_polynomial {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖iteratedDeriv 2 (zetaGaussianQuadraticIntegral T G) v‖ ≤
      (v ^ 2 * G ^ 4 / 4 + G ^ 2 / 2) * (Real.sqrt Real.pi * G) := by
  apply (norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le hT hG hGT v).trans
  have he : Real.exp (-(G * v) ^ 2 / 8) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (G * v)])
  calc
    _ = ((v ^ 2 * G ^ 4 / 4 + G ^ 2 / 2) * (Real.sqrt Real.pi * G)) *
        Real.exp (-(G * v) ^ 2 / 8) := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left he
        (show 0 ≤ (v ^ 2 * G ^ 4 / 4 + G ^ 2 / 2) * (Real.sqrt Real.pi * G) by positivity)
      simpa only [mul_one] using h

end MathCollab.Density.Stronger.Atkinson
