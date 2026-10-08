module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannTwoTermExpansion.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannLaplaceRemainder

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# A two-term expansion of the literal order-zero Neumann kernel

The phase is written in sine/cosine coordinates to expose both
oscillatory carriers directly. The error has the globally valid
positive-argument bound C x^(-5/2).
-/

set_option autoImplicit false
noncomputable section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

def neumannTwoTerm (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi / Real.pi) *
    ((Real.sin x - Real.cos x) * x ^ (-(1 / 2 : ℝ)) -
      (Real.sin x + Real.cos x) / 8 * x ^ (-(3 / 2 : ℝ)))

def neumannTwoTermErrorConstant : ℝ := (2 / Real.pi) * (9 / 128 : ℝ) * Real.sqrt Real.pi

theorem neumannTwoTermErrorConstant_pos : 0 < neumannTwoTermErrorConstant := by
  unfold neumannTwoTermErrorConstant
  positivity

theorem neumannTwoTerm_eq_ray_approximation (x : ℝ) :
    neumannTwoTerm x = -(2 / Real.pi) *
      (Complex.exp (I * (x : ℂ)) * neumannRayCoefficient * neumannLaplaceApproximation x).re := by
  rw [neumannRayCoefficient_eq]
  norm_num [neumannTwoTerm, neumannLaplaceApproximation, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im]
  ring

theorem abs_dfiBesselY0_sub_neumannTwoTerm_le {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0 x - neumannTwoTerm x| ≤ neumannTwoTermErrorConstant * x ^ (-(5 / 2 : ℝ)) := by
  have hcoef : ‖Complex.exp (I * (x : ℂ)) * neumannRayCoefficient‖ ≤ 1 := by
    rw [norm_mul]
    have he : ‖Complex.exp (I * (x : ℂ))‖ = 1 := by simp [Complex.norm_exp, mul_re]
    rw [he, one_mul]
    exact norm_neumannRayCoefficient_le_one
  have hp : ‖Complex.exp (I * (x : ℂ)) * neumannRayCoefficient *
      (neumannLaplaceIntegral x - neumannLaplaceApproximation x)‖ ≤
        (9 / 128 : ℝ) * Real.sqrt Real.pi * x ^ (-(5 / 2 : ℝ)) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * ((9 / 128 : ℝ) * Real.sqrt Real.pi * x ^ (-(5 / 2 : ℝ))) := by
        gcongr
        exact norm_neumannLaplaceIntegral_sub_approximation_le hx
      _ = _ := one_mul _
  have heq : dfiBesselY0 x - neumannTwoTerm x = -(2 / Real.pi) *
      (Complex.exp (I * (x : ℂ)) * neumannRayCoefficient *
        (neumannLaplaceIntegral x - neumannLaplaceApproximation x)).re := by
    rw [dfiBesselY0_eq_neumannLaplaceIntegral hx, neumannTwoTerm_eq_ray_approximation]
    simp only [mul_sub, Complex.sub_re]
  rw [heq, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
  have h := mul_le_mul_of_nonneg_left
    ((Complex.abs_re_le_norm _).trans hp) (by positivity : 0 ≤ 2 / Real.pi)
  convert h using 1
  unfold neumannTwoTermErrorConstant
  ring

end MathCollab.Density.Stronger.Atkinson
