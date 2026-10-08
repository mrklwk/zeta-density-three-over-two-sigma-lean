module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannSchlafliEntry.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannContourShift

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Matching the contour to the existing Schläfli integral

The imaginary-axis ray is exactly the real decaying term. The
real-axis segment becomes the actual sine integral, with the
endpoint singularity handled by a nonsingular angular parameter.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval ComplexConjugate

namespace MathCollab.Density.Stronger.Atkinson

theorem continuousAt_neumannVerticalIntegral {x b : ℝ}
    (hx : 0 < x) (hb : 0 < b) : ContinuousAt (neumannVerticalIntegral x) b := by
  unfold neumannVerticalIntegral
  have hnear : ∀ᶠ c : ℝ in 𝓝 b, 0 < c := isOpen_Ioi.mem_nhds hb
  apply continuousAt_of_dominated (bound := fun t : ℝ =>
    t ^ (-(1 / 2 : ℝ)) * Real.exp (-x * t))
  · filter_upwards [hnear] with c hc
    exact (integrableOn_neumannContourKernel_vertical hx hc.le).aestronglyMeasurable
  · filter_upwards [hnear] with c hc
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [mul_comm] using norm_neumannContourKernel_vertical_le hc.le ht
  · simpa only [Real.rpow_one] using!
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : -1 < -(1 / 2 : ℝ))
        (by norm_num : 0 < (1 : ℝ)) hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs := neumannContourKernel_slit_vertical hb.le ht
    exact (differentiableAt_neumannContourKernel x hs.1 hs.2).continuousAt.comp
      (f := fun c : ℝ => (c : ℂ) + t * I) (by fun_prop)

theorem neumannContourHalfPowers_imaginary_axis (t : ℝ) :
    (1 - (t : ℂ) * I) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) * I) ^ (-(1 / 2 : ℂ)) =
        ((Real.sqrt (1 + t ^ 2))⁻¹ : ℝ) := by
  let z : ℂ := 1 + (t : ℂ) * I
  have hz : z ∈ slitPlane := Or.inl (by simp [z])
  have hc : (1 - (t : ℂ) * I) ^ (-(1 / 2 : ℂ)) =
      conj (z ^ (-(1 / 2 : ℂ))) := by
    have h := Complex.conj_cpow z (-(1 / 2 : ℂ)) (slitPlane_arg_ne_pi hz)
    simpa [z, sub_eq_add_neg, map_ofNat] using h
  have hn : ‖z ^ (-(1 / 2 : ℂ))‖ = ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    convert Complex.norm_cpow_real z (-(1 / 2 : ℝ)) using 1
    norm_num
  have hs : ‖z ^ (-(1 / 2 : ℂ))‖ ^ 2 = ‖z‖⁻¹ := by
    calc
      _ = (‖z‖ ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by rw [hn, Real.rpow_two]
      _ = ‖z‖ ^ (-1 : ℝ) := by rw [← Real.rpow_mul (norm_nonneg z)]; norm_num
      _ = _ := Real.rpow_neg_one _
  have hzNorm : ‖z‖ = Real.sqrt (1 + t ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [z, normSq_apply, pow_two]
  change (1 - (t : ℂ) * I) ^ (-(1 / 2 : ℂ)) * z ^ (-(1 / 2 : ℂ)) = _
  rw [hc, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hs, hzNorm]

theorem neumannContourKernel_imaginary_axis (x t : ℝ) :
    neumannContourKernel x ((t : ℂ) * I) =
      (Real.exp (-x * t) / Real.sqrt (1 + t ^ 2) : ℝ) := by
  have he : I * (x : ℂ) * ((t : ℂ) * I) = ((-x * t : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (x : ℂ) * t * (I * I) := by ring
      _ = _ := by rw [I_mul_I]; ring
  unfold neumannContourKernel
  rw [mul_assoc, neumannContourHalfPowers_imaginary_axis, he, ← Complex.ofReal_exp]
  push_cast
  ring

theorem neumannVerticalIntegral_zero_eq_tail (x : ℝ) :
    neumannVerticalIntegral x 0 = (dfiBesselY0Tail x : ℂ) := by
  unfold neumannVerticalIntegral dfiBesselY0Tail
  simp only [Complex.ofReal_zero, zero_add, neumannContourKernel_imaginary_axis]
  exact integral_complex_ofReal

theorem neumannContourHalfPowers_sine {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u < Real.pi / 2) :
    (Real.cos u : ℂ) *
      ((1 - (Real.sin u : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (1 + (Real.sin u : ℂ)) ^ (-(1 / 2 : ℂ))) = 1 := by
  have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hu1⟩
  have hs : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu (by linarith [Real.pi_pos])
  have hm : 0 ≤ 1 - Real.sin u := sub_nonneg.mpr (Real.sin_le_one u)
  have hp : 0 ≤ 1 + Real.sin u := by linarith
  have hprod : (1 - Real.sin u) * (1 + Real.sin u) = (Real.cos u) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hmul := Complex.mul_cpow_ofReal_nonneg hm hp (-(1 / 2 : ℂ))
  have hpow : (((Real.cos u) ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
      (((Real.cos u)⁻¹ : ℝ) : ℂ) := by
    have hh := Complex.ofReal_cpow (sq_nonneg (Real.cos u)) (-(1 / 2 : ℝ))
    norm_num only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] at hh
    rw [← hh, Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]
  have hminus : (1 - (Real.sin u : ℂ)) = ((1 - Real.sin u : ℝ) : ℂ) := by push_cast; rfl
  have hplus : (1 + (Real.sin u : ℂ)) = ((1 + Real.sin u : ℝ) : ℂ) := by push_cast; rfl
  rw [hminus, hplus, ← hmul, ← Complex.ofReal_mul, hprod, hpow]
  norm_cast
  exact mul_inv_cancel₀ hc.ne'

theorem neumannContourKernel_angular_change (x : ℝ) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < Real.pi / 2) :
    (∫ u in (0 : ℝ)..Real.sin a, neumannContourKernel x u) =
      ∫ u in (0 : ℝ)..a, Complex.exp (I * (x : ℂ) * Real.sin u) := by
  have hc := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun y : ℝ => neumannContourKernel x y)
    (f := Real.sin) (f' := Real.cos) (a := (0 : ℝ)) (b := a)
    Real.continuous_sin.continuousOn
    (fun u _ => Real.hasDerivAt_sin u)
    (fun u hu => (Real.cos_pos_of_mem_Ioo ⟨by
      rw [min_eq_left ha, max_eq_right ha] at hu
      linarith [hu.1, Real.pi_pos], by
      rw [min_eq_left ha, max_eq_right ha] at hu
      linarith [hu.2]⟩).le)
  rw [Real.sin_zero] at hc
  rw [← hc]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha] at hu
  have hp := neumannContourHalfPowers_sine hu.1 (lt_of_le_of_lt hu.2 ha1)
  simp only [Function.comp_apply, neumannContourKernel, real_smul]
  calc
    _ = Complex.exp (I * (x : ℂ) * Real.sin u) *
        ((Real.cos u : ℂ) * ((1 - (Real.sin u : ℂ)) ^ (-(1 / 2 : ℂ)) *
          (1 + (Real.sin u : ℂ)) ^ (-(1 / 2 : ℂ)))) := by ring
    _ = _ := by rw [hp, mul_one]

end MathCollab.Density.Stronger.Atkinson
