module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannRayFactorization.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannLaplaceAmplitude

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Factoring the genuine Neumann ray into its decaying Laplace integral

The coefficient remains an explicit principal complex half-power.
The angular phase, arithmetic normalization and entire amplitude
are retained exactly.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem neumann_cpow_positive_real_mul {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ≠ 0) (s : ℂ) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz),
    Complex.log_ofReal_mul hr hz, Complex.ofReal_log hr.le,
    add_mul, Complex.exp_add, ← Complex.cpow_def_of_ne_zero hr0,
    ← Complex.cpow_def_of_ne_zero hz]

def neumannRayCoefficient : ℂ := (-I) ^ (-(1 / 2 : ℂ)) * (2 : ℂ) ^ (-(1 / 2 : ℂ))

def neumannLaplaceIntegrand (x t : ℝ) : ℂ :=
  ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-x * t) : ℝ) : ℂ) * neumannLaplaceAmplitude (t / 2)

def neumannLaplaceIntegral (x : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, neumannLaplaceIntegrand x t

theorem continuous_neumannLaplaceAmplitude : Continuous neumannLaplaceAmplitude := by
  rw [continuous_iff_continuousAt]
  intro u
  have hpow : DifferentiableAt ℂ (fun z : ℂ => z ^ (-(1 / 2 : ℂ))) (1 + (u : ℂ) * I) :=
    differentiableAt_id.cpow_const (Or.inl (by simp : 0 < (1 + (u : ℂ) * I).re))
  exact hpow.continuousAt.comp
      (f := fun v : ℝ => 1 + (v : ℂ) * I) (by fun_prop)

theorem neumannContourKernel_unit_ray (x : ℝ) {t : ℝ} (ht : 0 < t) :
    neumannContourKernel x (1 + (t : ℂ) * I) =
      Complex.exp (I * (x : ℂ)) * neumannRayCoefficient * neumannLaplaceIntegrand x t := by
  have hm : 1 - (1 + (t : ℂ) * I) = (t : ℂ) * (-I) := by ring
  have hp : 1 + (1 + (t : ℂ) * I) = (2 : ℂ) * (1 + (t / 2 : ℝ) * I) := by
    push_cast
    ring
  have hp0 : (1 + (t / 2 : ℝ) * I : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hpow : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have h := Complex.ofReal_cpow ht.le (-(1 / 2 : ℝ))
    norm_num only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] at h
    exact h.symm
  have he : Complex.exp (I * (x : ℂ) * (1 + (t : ℂ) * I)) =
      Complex.exp (I * (x : ℂ)) * (Real.exp (-x * t) : ℝ) := by
    have harg : I * (x : ℂ) * (1 + (t : ℂ) * I) =
        I * (x : ℂ) + ((-x * t : ℝ) : ℂ) := by
      push_cast
      calc
        _ = I * (x : ℂ) + (x : ℂ) * t * (I * I) := by ring
        _ = _ := by rw [I_mul_I]; ring
    rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  unfold neumannContourKernel
  have htwo := neumann_cpow_positive_real_mul (by norm_num : (0 : ℝ) < 2) hp0 (-(1 / 2 : ℂ))
  norm_num only [Complex.ofReal_ofNat] at htwo
  rw [hm, hp, neumann_cpow_positive_real_mul ht (neg_ne_zero.mpr I_ne_zero),
    htwo, hpow, he]
  unfold neumannRayCoefficient neumannLaplaceIntegrand neumannLaplaceAmplitude
  push_cast
  ring

theorem norm_neumannLaplaceIntegrand_le (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖neumannLaplaceIntegrand x t‖ ≤ t ^ (-(1 / 2 : ℝ)) * Real.exp (-x * t) := by
  rw [neumannLaplaceIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ t ^ (-(1 / 2 : ℝ)) * Real.exp (-x * t))]
  exact mul_le_of_le_one_right (by positivity) (norm_neumannLaplaceAmplitude_le_one _)

theorem integrableOn_neumannLaplaceIntegrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (neumannLaplaceIntegrand x) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-x * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : -1 < -(1 / 2 : ℝ))
        (by norm_num : 0 < (1 : ℝ)) hx
  have hm : AEStronglyMeasurable (neumannLaplaceIntegrand x) (volume.restrict (Ioi 0)) := by
    unfold neumannLaplaceIntegrand
    apply AEStronglyMeasurable.mul
    · exact (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable
    · exact (continuous_neumannLaplaceAmplitude.comp (by fun_prop)).aestronglyMeasurable
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_neumannLaplaceIntegrand_le x ht.le

theorem neumannVerticalIntegral_one_eq_laplace (x : ℝ) :
    neumannVerticalIntegral x 1 =
      Complex.exp (I * (x : ℂ)) * neumannRayCoefficient * neumannLaplaceIntegral x := by
  unfold neumannVerticalIntegral neumannLaplaceIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact neumannContourKernel_unit_ray x ht

theorem dfiBesselY0_eq_neumannLaplaceIntegral {x : ℝ} (hx : 0 < x) :
    dfiBesselY0 x = -(2 / Real.pi) *
      (Complex.exp (I * (x : ℂ)) * neumannRayCoefficient * neumannLaplaceIntegral x).re := by
  rw [dfiBesselY0_eq_neumannVerticalIntegral hx, neumannVerticalIntegral_one_eq_laplace]

end MathCollab.Density.Stronger.Atkinson
