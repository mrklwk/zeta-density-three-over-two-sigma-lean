module
-- Reversible module-visibility port of the audited development.
/-
A direct positive-argument bound for the literal Schläfli Y0 kernel,
derived from the verified decaying-ray representation. This proof uses
no oscillatory asymptotic as a premise. Selected source definitions and
ray lemmas retain the McColm MIT-0 attribution; see third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannLaplaceMoments

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_neumannLaplaceIntegral_le {x : ℝ} (hx : 0 < x) :
    ‖neumannLaplaceIntegral x‖ ≤ Real.sqrt Real.pi * x ^ (-(1 / 2 : ℝ)) := by
  have h := norm_integral_le_of_norm_le
    (integrableOn_neumannLaplaceMomentIntegrand hx 0)
    (f := neumannLaplaceIntegrand x)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [neumannLaplaceMomentIntegrand, Nat.cast_zero, zero_sub] using
        norm_neumannLaplaceIntegrand_le x ht.le)
  change ‖neumannLaplaceIntegral x‖ ≤ neumannLaplaceMoment x 0 at h
  rwa [neumannLaplaceMoment_zero hx] at h

theorem abs_dfiBesselY0_le_seven_div_sqrt {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0 x| ≤ 7 / Real.sqrt x := by
  have hcoef : ‖Complex.exp (I * (x : ℂ)) * neumannRayCoefficient‖ ≤ 1 := by
    rw [norm_mul]
    have he : ‖Complex.exp (I * (x : ℂ))‖ = 1 := by simp [Complex.norm_exp, mul_re]
    rw [he, one_mul]
    exact norm_neumannRayCoefficient_le_one
  have hc : (2 / Real.pi) * Real.sqrt Real.pi ≤ 7 := by
    have hs : Real.sqrt Real.pi ≤ Real.pi := by
      nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_gt_three]
    calc
      _ ≤ (2 / Real.pi) * Real.pi := by gcongr
      _ = 2 := by field_simp
      _ ≤ 7 := by norm_num
  rw [dfiBesselY0_eq_neumannLaplaceIntegral hx, abs_mul, abs_neg,
    abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
  calc
    _ ≤ (2 / Real.pi) * ‖Complex.exp (I * (x : ℂ)) * neumannRayCoefficient *
        neumannLaplaceIntegral x‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ (2 / Real.pi) * (Real.sqrt Real.pi * x ^ (-(1 / 2 : ℝ))) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul hcoef (norm_neumannLaplaceIntegral_le hx) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul _)) (by positivity)
    _ ≤ 7 * x ^ (-(1 / 2 : ℝ)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx.le _)
    _ = _ := by rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

end MathCollab.Density.Stronger.Atkinson
