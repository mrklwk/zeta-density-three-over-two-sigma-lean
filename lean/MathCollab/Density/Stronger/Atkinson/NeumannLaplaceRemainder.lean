module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannLaplaceRemainder.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannLaplaceMoments

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Integrating the proved quadratic remainder on the Neumann ray

The approximation is obtained by integrating the actual constant
and linear amplitude terms. The quadratic error is integrable and
has its exact x^(-5/2) scale.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def neumannLaplaceApproximation (x : ℝ) : ℂ :=
  ((Real.sqrt Real.pi * x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) -
    I / 8 * ((Real.sqrt Real.pi * x ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)

theorem norm_neumannLaplaceIntegrand_sub_linear_le (x : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖neumannLaplaceIntegrand x t - (neumannLaplaceMomentIntegrand x 0 t : ℂ) +
      I / 4 * (neumannLaplaceMomentIntegrand x 1 t : ℂ)‖ ≤
        (3 / 32 : ℝ) * neumannLaplaceMomentIntegrand x 2 t := by
  have h0 : neumannLaplaceIntegrand x t =
      (neumannLaplaceMomentIntegrand x 0 t : ℂ) * neumannLaplaceAmplitude (t / 2) := by
    simp only [neumannLaplaceIntegrand, neumannLaplaceMomentIntegrand, Nat.cast_zero, zero_sub]
  have h1 := neumannLaplaceMomentIntegrand_eq_mul x 1 ht
  have h2 := neumannLaplaceMomentIntegrand_eq_mul x 2 ht
  have he : neumannLaplaceIntegrand x t - (neumannLaplaceMomentIntegrand x 0 t : ℂ) +
      I / 4 * (neumannLaplaceMomentIntegrand x 1 t : ℂ) =
        (neumannLaplaceMomentIntegrand x 0 t : ℂ) *
          (neumannLaplaceAmplitude (t / 2) - 1 + (t / 2 : ℝ) * I / 2) := by
    rw [h0, h1]
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (neumannLaplaceMomentIntegrand_nonneg ht.le 0)]
  calc
    _ ≤ neumannLaplaceMomentIntegrand x 0 t * ((3 / 8 : ℝ) * (t / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_neumannLaplaceAmplitude_sub_linear_le _)
        (neumannLaplaceMomentIntegrand_nonneg ht.le 0)
    _ = _ := by rw [h2]; ring

theorem norm_neumannLaplaceIntegral_sub_moments_le {x : ℝ} (hx : 0 < x) :
    ‖neumannLaplaceIntegral x -
      ((neumannLaplaceMoment x 0 : ℂ) - I / 4 * (neumannLaplaceMoment x 1 : ℂ))‖ ≤
        (3 / 32 : ℝ) * neumannLaplaceMoment x 2 := by
  have hi0 : IntegrableOn (fun t : ℝ => (neumannLaplaceMomentIntegrand x 0 t : ℂ)) (Ioi 0) :=
    (integrableOn_neumannLaplaceMomentIntegrand hx 0).ofReal
  have hi1 : IntegrableOn (fun t : ℝ => (neumannLaplaceMomentIntegrand x 1 t : ℂ)) (Ioi 0) :=
    (integrableOn_neumannLaplaceMomentIntegrand hx 1).ofReal
  have hj := integrableOn_neumannLaplaceIntegrand hx
  have hiSub : IntegrableOn (fun t : ℝ => neumannLaplaceIntegrand x t -
      (neumannLaplaceMomentIntegrand x 0 t : ℂ)) (Ioi 0) := hj.sub hi0
  have he : (∫ t : ℝ in Ioi 0, neumannLaplaceIntegrand x t -
      (neumannLaplaceMomentIntegrand x 0 t : ℂ) + I / 4 * (neumannLaplaceMomentIntegrand x 1 t : ℂ)) =
        neumannLaplaceIntegral x -
          ((neumannLaplaceMoment x 0 : ℂ) - I / 4 * (neumannLaplaceMoment x 1 : ℂ)) := by
    rw [integral_add hiSub (hi1.const_mul (I / 4)), integral_sub hj hi0, integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal]
    unfold neumannLaplaceIntegral neumannLaplaceMoment
    ring
  rw [← he]
  have h := norm_integral_le_of_norm_le
    ((integrableOn_neumannLaplaceMomentIntegrand hx 2).const_mul (3 / 32 : ℝ))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_neumannLaplaceIntegrand_sub_linear_le x ht)
  simpa only [integral_const_mul, neumannLaplaceMoment] using h

theorem norm_neumannLaplaceIntegral_sub_approximation_le {x : ℝ} (hx : 0 < x) :
    ‖neumannLaplaceIntegral x - neumannLaplaceApproximation x‖ ≤
      (9 / 128 : ℝ) * Real.sqrt Real.pi * x ^ (-(5 / 2 : ℝ)) := by
  have h := norm_neumannLaplaceIntegral_sub_moments_le hx
  rw [neumannLaplaceMoment_zero hx, neumannLaplaceMoment_one hx,
    neumannLaplaceMoment_two hx] at h
  have he : ((Real.sqrt Real.pi * x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) -
      I / 4 * (((Real.sqrt Real.pi / 2) * x ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) =
        neumannLaplaceApproximation x := by
    unfold neumannLaplaceApproximation
    push_cast
    ring
  rw [he] at h
  convert h using 1
  ring

end MathCollab.Density.Stronger.Atkinson
