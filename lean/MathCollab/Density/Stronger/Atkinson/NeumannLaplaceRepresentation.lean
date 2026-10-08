module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannLaplaceRepresentation.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannSchlafliEntry
public import Mathlib.Analysis.Real.Pi.Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# An exact decaying-ray representation of the literal Neumann kernel

This is proved from the existing Schläfli definition, not adopted as
a new definition of Y0. All principal-power branches and limiting
integrals enter through the proved contour and angular bridges.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace MathCollab.Density.Stronger.Atkinson

theorem neumann_sine_integral_eq_cosine (x : ℝ) :
    (∫ u in (0 : ℝ)..Real.pi / 2, Complex.exp (I * (x : ℂ) * Real.sin u)) =
      ∫ u in (0 : ℝ)..Real.pi / 2, Complex.exp (I * (x : ℂ) * Real.cos u) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => Complex.exp (I * (x : ℂ) * Real.cos u))
    (a := (0 : ℝ)) (b := Real.pi / 2) (Real.pi / 2)
  simpa only [Real.cos_pi_div_two_sub, sub_self, sub_zero] using h

theorem neumann_schlafli_complex_identity {x : ℝ} (hx : 0 < x) :
    (∫ u in (0 : ℝ)..Real.pi / 2, Complex.exp (I * (x : ℂ) * Real.cos u)) =
      I * neumannVerticalIntegral x 0 - I * neumannVerticalIntegral x 1 := by
  let a : ℝ → ℝ := fun H => Real.pi / 2 - H⁻¹
  have ha : Tendsto a atTop (𝓝 (Real.pi / 2)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := Real.pi / 2)).sub tendsto_inv_atTop_zero
  have hs : Tendsto (fun H => Real.sin (a H)) atTop (𝓝 1) := by
    simpa only [Real.sin_pi_div_two] using! Real.continuous_sin.continuousAt.tendsto.comp ha
  have hf : Continuous (fun u : ℝ => Complex.exp (I * (x : ℂ) * Real.sin u)) := by fun_prop
  have hl := (hf.integral_hasStrictDerivAt (0 : ℝ) (Real.pi / 2)).hasDerivAt.continuousAt.tendsto.comp ha
  have hr := (tendsto_const_nhds (x := I * neumannVerticalIntegral x 0)).sub
    (((continuousAt_neumannVerticalIntegral hx (by norm_num : (0 : ℝ) < 1)).tendsto.comp hs).const_mul I)
  have heq : ∀ᶠ H : ℝ in atTop,
      (∫ u in (0 : ℝ)..a H, Complex.exp (I * (x : ℂ) * Real.sin u)) =
        I * neumannVerticalIntegral x 0 - I * neumannVerticalIntegral x (Real.sin (a H)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hH0 : 0 < H := by linarith
    have hInv : H⁻¹ ≤ 1 := (inv_le_one₀ hH0).2 hH
    have ha0 : 0 ≤ a H := by dsimp [a]; linarith [Real.pi_gt_three]
    have ha1 : a H < Real.pi / 2 := by dsimp [a]; linarith [inv_pos.mpr hH0]
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith [Real.pi_pos])
    have hs1 : Real.sin (a H) < 1 := by
      have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ a H) (le_refl (Real.pi / 2)) ha1
      simpa only [Real.sin_pi_div_two] using h
    rw [← neumannContourKernel_angular_change x ha0 ha1]
    exact neumannContourKernel_infinite_rectangle hx hs0 hs1
  have hid : (∫ u in (0 : ℝ)..Real.pi / 2, Complex.exp (I * (x : ℂ) * Real.sin u)) =
      I * neumannVerticalIntegral x 0 - I * neumannVerticalIntegral x 1 :=
    tendsto_nhds_unique hl (hr.congr' (heq.mono (fun _ h => h.symm)))
  rwa [neumann_sine_integral_eq_cosine] at hid

theorem dfiBesselY0_eq_neumannVerticalIntegral {x : ℝ} (hx : 0 < x) :
    dfiBesselY0 x = -(2 / Real.pi) * (neumannVerticalIntegral x 1).re := by
  have h := congrArg Complex.im (neumann_schlafli_complex_identity hx)
  rw [neumannVerticalIntegral_zero_eq_tail] at h
  have he : (∫ u in (0 : ℝ)..Real.pi / 2, Complex.exp (I * (x : ℂ) * Real.cos u)).im =
      dfiBesselY0Osc x := by
    unfold dfiBesselY0Osc
    congr 2
    funext u
    congr 1
    push_cast
    ring
  rw [he] at h
  simp only [sub_im, mul_im, I_re, I_im, ofReal_im, ofReal_re, zero_mul, one_mul, zero_add] at h
  rw [dfiBesselY0, h]
  ring

end MathCollab.Density.Stronger.Atkinson
