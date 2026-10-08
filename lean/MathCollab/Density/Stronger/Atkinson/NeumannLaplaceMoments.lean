module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannLaplaceMoments.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannRayFactorization

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Exact Gaussian-half-line moments of the decaying Neumann ray

The three actual Laplace moments give the two leading terms and the
integrable quadratic remainder. All identities hold for every x > 0.
-/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def neumannLaplaceMomentIntegrand (x : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t ^ ((k : ℝ) - 1 / 2) * Real.exp (-x * t)

def neumannLaplaceMoment (x : ℝ) (k : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi 0, neumannLaplaceMomentIntegrand x k t

theorem integrableOn_neumannLaplaceMomentIntegrand {x : ℝ} (hx : 0 < x) (k : ℕ) :
    IntegrableOn (neumannLaplaceMomentIntegrand x k) (Ioi 0) := by
  simpa only [neumannLaplaceMomentIntegrand, Real.rpow_one] using!
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith : -1 < (k : ℝ) - 1 / 2)
      (by norm_num : 0 < (1 : ℝ)) hx

theorem neumannLaplaceMomentIntegrand_nonneg {x t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ neumannLaplaceMomentIntegrand x k t := by
  unfold neumannLaplaceMomentIntegrand
  positivity

theorem neumannLaplaceMomentIntegrand_eq_mul (x : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    neumannLaplaceMomentIntegrand x k t =
      neumannLaplaceMomentIntegrand x 0 t * t ^ k := by
  unfold neumannLaplaceMomentIntegrand
  rw [show (k : ℝ) - 1 / 2 = -(1 / 2 : ℝ) + k by ring, Real.rpow_add ht, Real.rpow_natCast]
  norm_num
  ring

theorem neumannLaplaceMoment_eq_gamma {x : ℝ} (hx : 0 < x) (k : ℕ) :
    neumannLaplaceMoment x k =
      x ^ (-((k : ℝ) + 1 / 2)) * Real.Gamma ((k : ℝ) + 1 / 2) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by positivity : 0 < (k : ℝ) + 1 / 2) hx
  have he : (k : ℝ) + 1 / 2 - 1 = (k : ℝ) - 1 / 2 := by ring
  rw [he] at h
  simpa only [neumannLaplaceMoment, neumannLaplaceMomentIntegrand, neg_mul,
    one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le] using h

theorem neumannLaplaceMoment_zero {x : ℝ} (hx : 0 < x) :
    neumannLaplaceMoment x 0 = Real.sqrt Real.pi * x ^ (-(1 / 2 : ℝ)) := by
  rw [neumannLaplaceMoment_eq_gamma hx]
  norm_num [Real.Gamma_one_half_eq, mul_comm]

theorem neumannLaplaceMoment_one {x : ℝ} (hx : 0 < x) :
    neumannLaplaceMoment x 1 = (Real.sqrt Real.pi / 2) * x ^ (-(3 / 2 : ℝ)) := by
  have hg := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  rw [Real.Gamma_one_half_eq] at hg
  rw [neumannLaplaceMoment_eq_gamma hx]
  norm_num at hg ⊢
  rw [hg]
  ring

theorem neumannLaplaceMoment_two {x : ℝ} (hx : 0 < x) :
    neumannLaplaceMoment x 2 = (3 * Real.sqrt Real.pi / 4) * x ^ (-(5 / 2 : ℝ)) := by
  have hg := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  have hg' := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
  rw [Real.Gamma_one_half_eq] at hg
  norm_num at hg hg'
  rw [hg] at hg'
  rw [neumannLaplaceMoment_eq_gamma hx]
  norm_num
  rw [hg']
  ring

theorem neumannRayCoefficient_eq : neumannRayCoefficient = (1 + I) / 2 := by
  have hp := neumann_cpow_positive_real_mul (by norm_num : (0 : ℝ) < 2)
    (neg_ne_zero.mpr I_ne_zero) (-(1 / 2 : ℂ))
  norm_num only [Complex.ofReal_ofNat] at hp
  have hsq : (1 - I) ^ 2 = (2 : ℂ) * (-I) := by
    calc
      _ = 1 - 2 * I + I * I := by ring
      _ = _ := by rw [I_mul_I]; ring
  unfold neumannRayCoefficient
  rw [mul_comm, ← hp, ← hsq, Complex.cpow_neg, one_div,
    Complex.sq_cpow_two_inv (by simp : 0 < (1 - I).re)]
  apply inv_eq_of_mul_eq_one_right
  calc
    _ = (1 - I * I) / 2 := by ring
    _ = 1 := by rw [I_mul_I]; norm_num

theorem norm_neumannRayCoefficient_le_one : ‖neumannRayCoefficient‖ ≤ 1 := by
  rw [neumannRayCoefficient_eq, norm_div]
  have h := norm_add_le (1 : ℂ) I
  norm_num at h ⊢
  linarith

end MathCollab.Density.Stronger.Atkinson
