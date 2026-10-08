module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannLaplaceAmplitude.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannLaplaceRepresentation
public import Mathlib.Analysis.RCLike.Sqrt

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# A global quadratic remainder for the complex Laplace amplitude

The inverse square root is the principal one. Its first-order
approximation and a uniform quadratic error are derived algebraically
from the actual square root, not supplied as an asymptotic premise.
-/

set_option autoImplicit false
noncomputable section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

def neumannLaplaceAmplitude (u : ℝ) : ℂ :=
  (1 + (u : ℂ) * I) ^ (-(1 / 2 : ℂ))

theorem neumannLaplaceAmplitude_zero : neumannLaplaceAmplitude 0 = 1 := by
  simp [neumannLaplaceAmplitude]

theorem norm_neumannLaplaceAmplitude_le_one (u : ℝ) :
    ‖neumannLaplaceAmplitude u‖ ≤ 1 := by
  have hz : 1 ≤ ‖1 + (u : ℂ) * I‖ := by
    simpa using Complex.re_le_norm (1 + (u : ℂ) * I)
  have hn : ‖neumannLaplaceAmplitude u‖ = ‖1 + (u : ℂ) * I‖ ^ (-(1 / 2 : ℝ)) := by
    unfold neumannLaplaceAmplitude
    convert Complex.norm_cpow_real (1 + (u : ℂ) * I) (-(1 / 2 : ℝ)) using 1
    norm_num
  rw [hn]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_of_nonpos zero_lt_one hz (by norm_num : -(1 / 2 : ℝ) ≤ 0)

theorem neumann_sqrt_re_ge_one (u : ℝ) :
    1 ≤ ((1 + (u : ℂ) * I) ^ (1 / 2 : ℂ)).re := by
  have hz : 1 ≤ ‖1 + (u : ℂ) * I‖ := by
    simpa using Complex.re_le_norm (1 + (u : ℂ) * I)
  rw [one_div, Complex.cpow_inv_two_re]
  have hr : (1 + (u : ℂ) * I).re = 1 := by simp
  rw [hr]
  exact (Real.one_le_sqrt).2 (by linarith)

theorem norm_neumannLaplaceAmplitude_sub_linear_le (u : ℝ) :
    ‖neumannLaplaceAmplitude u - 1 + (u : ℂ) * I / 2‖ ≤ (3 / 8 : ℝ) * u ^ 2 := by
  let w : ℂ := (1 + (u : ℂ) * I) ^ (1 / 2 : ℂ)
  have hwRe : 1 ≤ w.re := neumann_sqrt_re_ge_one u
  have hwn : 1 ≤ ‖w‖ := hwRe.trans (Complex.re_le_norm w)
  have hw : w ≠ 0 := by
    intro he
    simp only [he, zero_re] at hwRe
    linarith
  have hw1n : 2 ≤ ‖w + 1‖ := by
    have h := Complex.re_le_norm (w + 1)
    simp only [add_re, one_re] at h
    linarith
  have hw1 : w + 1 ≠ 0 := by
    intro he
    rw [he, norm_zero] at hw1n
    linarith
  have hsq : w ^ 2 = 1 + (u : ℂ) * I := by
    dsimp [w]
    rw [← Complex.cpow_mul_nat]
    norm_num
  have ha : neumannLaplaceAmplitude u = w⁻¹ := by
    exact Complex.cpow_neg _ _
  have hdiff : w - 1 = (u : ℂ) * I / (w + 1) := by
    apply (eq_div_iff hw1).2
    linear_combination hsq
  have hd : ‖w - 1‖ ≤ |u| / 2 := by
    rw [hdiff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
    exact div_le_div_of_nonneg_left (abs_nonneg u) (by norm_num) hw1n
  have hd2 : ‖w - 1‖ ^ 2 ≤ u ^ 2 / 4 := by
    have h := mul_self_le_mul_self (norm_nonneg (w - 1)) hd
    nlinarith [sq_abs u]
  have hlin : (u : ℂ) * I = w ^ 2 - 1 := by linear_combination -hsq
  have heq : (2 : ℂ) * w * (neumannLaplaceAmplitude u - 1 + (u : ℂ) * I / 2) =
      (w - 1) ^ 2 * (w + 2) := by
    rw [ha, hlin]
    field_simp
    ring
  have heqNorm : 2 * ‖w‖ * ‖neumannLaplaceAmplitude u - 1 + (u : ℂ) * I / 2‖ =
      ‖w - 1‖ ^ 2 * ‖w + 2‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_ofNat] using congrArg norm heq
  have hplus : ‖w + 2‖ ≤ ‖w‖ + 2 := by
    simpa only [Complex.norm_ofNat] using norm_add_le w 2
  have hbound : 2 * ‖w‖ * ‖neumannLaplaceAmplitude u - 1 + (u : ℂ) * I / 2‖ ≤
      2 * ‖w‖ * ((3 / 8 : ℝ) * u ^ 2) := by
    rw [heqNorm]
    calc
      _ ≤ (u ^ 2 / 4) * (‖w‖ + 2) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hwn)]
  exact le_of_mul_le_mul_left hbound (by positivity : 0 < 2 * ‖w‖)

end MathCollab.Density.Stronger.Atkinson
