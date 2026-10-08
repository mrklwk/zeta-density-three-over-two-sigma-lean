module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Provenance: ../../../../../third_party/twelfth/ATKINSON_GAUSSIAN_MANIFEST.json.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaGaussianQuadraticCoefficient (T G : ℝ) : ℂ :=
  ((1 / G ^ 2 : ℝ) : ℂ) + ((1 / (2 * T) : ℝ) : ℂ) * I

def zetaGaussianQuadraticIntegral (T G v : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (I * (v : ℂ) * x) *
    Complex.exp (-zetaGaussianQuadraticCoefficient T G * x ^ 2)

theorem zetaGaussianQuadraticCoefficient_re (T G : ℝ) :
    (zetaGaussianQuadraticCoefficient T G).re = 1 / G ^ 2 := by
  simp only [zetaGaussianQuadraticCoefficient, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_self, add_zero]

theorem zetaGaussianQuadraticCoefficient_im (T G : ℝ) :
    (zetaGaussianQuadraticCoefficient T G).im = 1 / (2 * T) := by
  simp only [zetaGaussianQuadraticCoefficient, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, zero_add]

theorem zetaGaussianQuadraticCoefficient_re_pos (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    0 < (zetaGaussianQuadraticCoefficient T G).re := by
  rw [zetaGaussianQuadraticCoefficient_re]
  positivity

theorem zetaGaussianQuadraticIntegral_eq (T v : ℝ) {G : ℝ} (hG : G ≠ 0) :
    zetaGaussianQuadraticIntegral T G v =
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-(v : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G)) :=
  fourierIntegral_gaussian (zetaGaussianQuadraticCoefficient_re_pos T hG) v

theorem integrable_zetaGaussianQuadraticIntegrand (T v : ℝ) {G : ℝ} (hG : G ≠ 0) :
    Integrable (fun x : ℝ => Complex.exp (I * (v : ℂ) * x) *
      Complex.exp (-zetaGaussianQuadraticCoefficient T G * x ^ 2)) := by
  have h := integrable_cexp_quadratic (zetaGaussianQuadraticCoefficient_re_pos T hG)
    (I * (v : ℂ)) 0
  convert h using 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  ring

theorem inverse_re_lower_of_im_le_re {a : ℂ} (ha : 0 < a.re) (hi : |a.im| ≤ a.re) :
    1 / (2 * a.re) ≤ a⁻¹.re := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hn : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  have hi2 : a.im ^ 2 ≤ a.re ^ 2 := by
    calc
      _ = |a.im| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [Complex.inv_re]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * a.re) hn).mpr
  rw [Complex.normSq_apply]
  nlinarith

theorem norm_fourierGaussian_le_of_im_le_re {a : ℂ} (ha : 0 < a.re)
    (hi : |a.im| ≤ a.re) (v : ℝ) :
    ‖((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) * Complex.exp (-(v : ℂ) ^ 2 / (4 * a))‖ ≤
      Real.sqrt (Real.pi / a.re) * Real.exp (-v ^ 2 / (8 * a.re)) := by
  have haNorm : a.re ≤ ‖a‖ := (le_abs_self _).trans (Complex.abs_re_le_norm a)
  have hexp : (-(v : ℂ) ^ 2 / (4 * a)).re = -(v ^ 2 / 4) * a⁻¹.re := by
    have heq : -(v : ℂ) ^ 2 / (4 * a) = ((-(v ^ 2 / 4) : ℝ) : ℂ) * a⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      push_cast
      ring
    rw [heq, Complex.re_ofReal_mul]
  have hdecay : -(v ^ 2 / 4) * a⁻¹.re ≤ -v ^ 2 / (8 * a.re) := by
    have h := mul_le_mul_of_nonpos_left (inverse_re_lower_of_im_le_re ha hi)
      (show -(v ^ 2 / 4) ≤ 0 from neg_nonpos.mpr (by positivity))
    convert h using 1
    field_simp
    ring
  rw [norm_mul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, ← Real.sqrt_eq_rpow, Complex.norm_exp, hexp]
  exact mul_le_mul (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left Real.pi_pos.le ha haNorm))
    (Real.exp_le_exp.mpr hdecay) (Real.exp_pos _).le (Real.sqrt_nonneg _)

/-- Uniform frequency damping in the physical range `G^2 ≤ 2T`. -/
theorem norm_zetaGaussianQuadraticIntegral_le {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hscale : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖zetaGaussianQuadraticIntegral T G v‖ ≤
      Real.sqrt Real.pi * G * Real.exp (-(G * v) ^ 2 / 8) := by
  have hi : |(zetaGaussianQuadraticCoefficient T G).im| ≤
      (zetaGaussianQuadraticCoefficient T G).re := by
    rw [zetaGaussianQuadraticCoefficient_im, zetaGaussianQuadraticCoefficient_re,
      abs_of_pos (by positivity : 0 < 1 / (2 * T))]
    exact one_div_le_one_div_of_le (by positivity) hscale
  rw [zetaGaussianQuadraticIntegral_eq T v hG.ne']
  have h := norm_fourierGaussian_le_of_im_le_re
    (zetaGaussianQuadraticCoefficient_re_pos T hG.ne') hi v
  have hden : Real.pi / (1 / G ^ 2) = Real.pi * G ^ 2 := by field_simp
  rw [zetaGaussianQuadraticCoefficient_re, hden, Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_sq_eq_abs, abs_of_pos hG] at h
  convert h using 1
  congr 2
  field_simp

theorem norm_zetaGaussianQuadraticIntegral_tail {T G L v : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hscale : G ^ 2 ≤ 2 * T)
    (hL : 0 ≤ L) (hfrequency : L ≤ G * |v|) :
    ‖zetaGaussianQuadraticIntegral T G v‖ ≤
      Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8) := by
  have hsq : L ^ 2 ≤ (G * v) ^ 2 := by
    calc
      _ ≤ (G * |v|) ^ 2 := pow_le_pow_left₀ hL hfrequency 2
      _ = _ := by rw [mul_pow, mul_pow, sq_abs]
  apply (norm_zetaGaussianQuadraticIntegral_le hT hG hscale v).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (by linarith)

theorem hasDerivAt_zetaGaussianQuadraticIntegral (T : ℝ) {G : ℝ} (hG : G ≠ 0) (v : ℝ) :
    HasDerivAt (zetaGaussianQuadraticIntegral T G)
      (-(v : ℂ) / (2 * zetaGaussianQuadraticCoefficient T G) *
        zetaGaussianQuadraticIntegral T G v) v := by
  have heq : zetaGaussianQuadraticIntegral T G = fun w : ℝ =>
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-(w : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G)) :=
    funext (fun w => zetaGaussianQuadraticIntegral_eq T w hG)
  have hv := (hasDerivAt_id v).ofReal_comp
  have h := ((hv.pow 2).neg.div_const (4 * zetaGaussianQuadraticCoefficient T G)).cexp.const_mul
    (((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ))
  rw [heq]
  convert h using 1 <;> simp only [Pi.pow_apply, Pi.neg_apply, id_eq, Complex.ofReal_one, Nat.reduceSub, pow_one, mul_one]
  ring

theorem inverse_norm_zetaGaussianQuadraticCoefficient_le (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    1 / ‖zetaGaussianQuadraticCoefficient T G‖ ≤ G ^ 2 := by
  have hr := zetaGaussianQuadraticCoefficient_re_pos T hG
  have hle := (Complex.re_le_norm (zetaGaussianQuadraticCoefficient T G))
  have h := one_div_le_one_div_of_le hr hle
  simpa only [zetaGaussianQuadraticCoefficient_re, one_div_one_div] using h

theorem norm_deriv_zetaGaussianQuadraticIntegral_le {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖deriv (zetaGaussianQuadraticIntegral T G) v‖ ≤
      (Real.sqrt Real.pi * G ^ 3 / 2) * |v| * Real.exp (-(G * v) ^ 2 / 8) := by
  rw [(hasDerivAt_zetaGaussianQuadraticIntegral T hG.ne' v).deriv, norm_mul,
    norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul]
  norm_num only [norm_ofNat]
  have hcoef : |v| / (2 * ‖zetaGaussianQuadraticCoefficient T G‖) ≤ |v| * G ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left (inverse_norm_zetaGaussianQuadraticCoefficient_le T hG.ne')
      (show 0 ≤ |v| / 2 by positivity)
    convert h using 1 <;> ring
  calc
    _ ≤ (|v| * G ^ 2 / 2) *
        (Real.sqrt Real.pi * G * Real.exp (-(G * v) ^ 2 / 8)) :=
      mul_le_mul hcoef (norm_zetaGaussianQuadraticIntegral_le hT hG hGT v)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
