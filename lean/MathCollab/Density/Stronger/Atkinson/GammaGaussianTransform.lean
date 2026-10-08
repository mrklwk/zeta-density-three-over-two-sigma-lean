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
public import MathCollab.Density.Stronger.Atkinson.GammaQuadratic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem integrable_physical_gaussian {G : ℝ} (hG : G ≠ 0) :
    Integrable (fun x : ℝ => Real.exp (-(x / G) ^ 2)) := by
  convert integrable_exp_neg_mul_sq (b := 1 / G ^ 2) (by positivity) using 1
  funext x
  congr 1
  ring

/-- A uniform physical Gaussian tail; its constant retains the width `G`. -/
theorem physical_gaussian_tail_le {G r : ℝ} (hG : 0 < G) (hr : 0 ≤ r) :
    (∫ x in (Ioc (-r) r)ᶜ, Real.exp (-(x / G) ^ 2)) ≤
      Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
  let K : ℝ → ℝ := fun x => Real.exp (-(1 / (2 * G ^ 2)) * x ^ 2)
  have hK : Integrable K := integrable_exp_neg_mul_sq (by positivity)
  have hmass : (∫ x : ℝ, K x) = Real.sqrt (2 * Real.pi) * G := by
    dsimp only [K]
    rw [integral_gaussian]
    rw [show Real.pi / (1 / (2 * G ^ 2)) = (2 * Real.pi) * G ^ 2 by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hG.le]
  calc
    _ ≤ ∫ x in (Ioc (-r) r)ᶜ, Real.exp (-(r / G) ^ 2 / 2) * K x := by
      apply integral_mono_ae (integrable_physical_gaussian hG.ne').integrableOn
        (hK.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with x hx
      have hrx : r ≤ |x| := by
        simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with hx | hx
        · exact (show r ≤ -x by linarith).trans (neg_le_abs x)
        · exact hx.le.trans (le_abs_self x)
      have hs : r ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
      dsimp only [K]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hd := div_le_div_of_nonneg_right hs (sq_nonneg G)
      simp only [div_pow]
      calc
        _ ≤ -(r ^ 2 / G ^ 2) / 2 - (x ^ 2 / G ^ 2) / 2 := by linarith
        _ = _ := by ring
    _ = Real.exp (-(r / G) ^ 2 / 2) * ∫ x in (Ioc (-r) r)ᶜ, K x := integral_const_mul _ _
    _ ≤ Real.exp (-(r / G) ^ 2 / 2) * ∫ x : ℝ, K x :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hK
        (Eventually.of_forall (fun x => (Real.exp_pos _).le))) (Real.exp_pos _).le
    _ = _ := by rw [hmass]; ring

private theorem norm_integral_sub_window_le {f : ℝ → ℂ} {G r : ℝ}
    (hG : 0 < G) (hr : 0 ≤ r) (hf : Integrable f)
    (hfn : ∀ x, ‖f x‖ ≤ Real.exp (-(x / G) ^ 2)) :
    ‖(∫ x : ℝ, f x) - ∫ x in -r..r, f x‖ ≤
      Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
  rw [intervalIntegral.integral_of_le (by linarith),
    ← setIntegral_compl measurableSet_Ioc hf]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact (integral_mono_ae hf.norm.integrableOn
    (integrable_physical_gaussian hG.ne').integrableOn
    (Eventually.of_forall hfn)).trans (physical_gaussian_tail_le hG hr)

def zetaSquareGammaGaussianIntegrand (T G v x : ℝ) : ℂ :=
  zetaSquareReflectedGammaPhase (T + x) * Complex.exp (I * (v : ℂ) * x) *
    ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)

def zetaSquareGammaGaussianTransform (T G v : ℝ) : ℂ :=
  ∫ x : ℝ, zetaSquareGammaGaussianIntegrand T G v x

theorem norm_zetaSquareGammaGaussianIntegrand (T G v x : ℝ) :
    ‖zetaSquareGammaGaussianIntegrand T G v x‖ = Real.exp (-(x / G) ^ 2) := by
  simp [zetaSquareGammaGaussianIntegrand, norm_zetaSquareReflectedGammaPhase, Complex.norm_exp]
  rw [← Complex.ofReal_div, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem integrable_zetaSquareGammaGaussianIntegrand (T v : ℝ) {G : ℝ} (hG : G ≠ 0) :
    Integrable (zetaSquareGammaGaussianIntegrand T G v) := by
  have hc : Continuous zetaSquareReflectedGammaPhase :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_zetaSquareReflectedGammaPhase t).continuousAt)
  have hf : Continuous (zetaSquareGammaGaussianIntegrand T G v) := by
    unfold zetaSquareGammaGaussianIntegrand
    fun_prop (disch := assumption)
  exact (integrable_physical_gaussian hG).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun x => (norm_zetaSquareGammaGaussianIntegrand T G v x).le))

private theorem norm_quadratic_gaussian_integrand (T v x : ℝ) {G : ℝ} (hG : G ≠ 0) :
    ‖Complex.exp (I * (v : ℂ) * x) *
      Complex.exp (-zetaGaussianQuadraticCoefficient T G * (x : ℂ) ^ 2)‖ =
      Real.exp (-(x / G) ^ 2) := by
  rw [norm_mul]
  have hunit : ‖Complex.exp (I * (v : ℂ) * (x : ℂ))‖ = 1 := by simp [Complex.norm_exp]
  rw [hunit, one_mul, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    zetaGaussianQuadraticCoefficient_re]
  field_simp

/-- The actual Gamma-phase transform is approximated by the proved quadratic
Gaussian transform, uniformly in frequency, with both omitted tails paid. -/
theorem norm_zetaSquareGammaGaussianTransform_sub_quadratic_le {T G r : ℝ}
    (hT : 4 ≤ T) (hG : 0 < G) (hr : 0 ≤ r) (hrT : r ≤ T / 2) (v : ℝ) :
    ‖zetaSquareGammaGaussianTransform T G v - zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi)))‖ ≤
      2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
        2 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
  let q := fun x : ℝ => Complex.exp (I * ((v - Real.log (T / (2 * Real.pi)) : ℝ) : ℂ) * x) *
    Complex.exp (-zetaGaussianQuadraticCoefficient T G * (x : ℂ) ^ 2)
  let F := ∫ x in -r..r, zetaSquareGammaGaussianIntegrand T G v x
  let Q := ∫ x in -r..r, q x
  have hleft := norm_integral_sub_window_le hG hr
    (integrable_zetaSquareGammaGaussianIntegrand T v hG.ne')
    (fun x => (norm_zetaSquareGammaGaussianIntegrand T G v x).le)
  have hright := norm_integral_sub_window_le hG hr
    (integrable_zetaGaussianQuadraticIntegrand T (v - Real.log (T / (2 * Real.pi))) hG.ne')
    (fun x => (norm_quadratic_gaussian_integrand T _ x hG.ne').le)
  have hmiddle := norm_integral_zetaSquareGammaPhase_sub_quadratic_le
    (G := G) hT hr hrT v
  change ‖F - zetaSquareReflectedGammaPhase T * Q‖ ≤ _ at hmiddle
  change ‖zetaSquareGammaGaussianTransform T G v - F‖ ≤ _ at hleft
  change ‖zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi))) - Q‖ ≤ _ at hright
  have hright' : ‖zetaSquareReflectedGammaPhase T * Q - zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi)))‖ ≤
      Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
    rw [← mul_sub, norm_mul, norm_zetaSquareReflectedGammaPhase, one_mul, norm_sub_rev]
    exact hright
  have htri := norm_sub_le_norm_sub_add_norm_sub (zetaSquareGammaGaussianTransform T G v) F
    (zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi))))
  have htri' := norm_sub_le_norm_sub_add_norm_sub F (zetaSquareReflectedGammaPhase T * Q)
    (zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi))))
  linarith

/-- The source-facing frequency damping of the genuine Gamma-phase integral.
The remaining amplitude/divisor source bridge is not a hypothesis here or
an output of this theorem. -/
theorem norm_zetaSquareGammaGaussianTransform_le {T G r : ℝ}
    (hT : 4 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hr : 0 ≤ r) (hrT : r ≤ T / 2) (v : ℝ) :
    ‖zetaSquareGammaGaussianTransform T G v‖ ≤
      Real.sqrt Real.pi * G * Real.exp (-(G * (v - Real.log (T / (2 * Real.pi)))) ^ 2 / 8) +
      2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
        2 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
  have herror := norm_zetaSquareGammaGaussianTransform_sub_quadratic_le hT hG hr hrT v
  have hmain := norm_zetaGaussianQuadraticIntegral_le (by linarith) hG hGT
    (v - Real.log (T / (2 * Real.pi)))
  have htri := norm_le_norm_sub_add (zetaSquareGammaGaussianTransform T G v)
    (zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi))))
  rw [norm_mul, norm_zetaSquareReflectedGammaPhase, one_mul] at htri
  linarith

end MathCollab.Density.Stronger.Atkinson
