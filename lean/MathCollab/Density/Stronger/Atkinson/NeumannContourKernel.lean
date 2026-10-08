module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannContourKernel.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselY0
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Complex.CauchyIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# The analytic contour behind the literal Neumann kernel

The two principal half-powers are kept separate. This fixes their
branches on the strip and exposes the integrable square-root
singularity as the right edge approaches one.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace MathCollab.Density.Stronger.Atkinson

def neumannContourKernel (x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (I * (x : ℂ) * z) *
    (1 - z) ^ (-(1 / 2 : ℂ)) * (1 + z) ^ (-(1 / 2 : ℂ))

theorem differentiableAt_neumannContourKernel (x : ℝ) {z : ℂ}
    (hminus : 1 - z ∈ slitPlane) (hplus : 1 + z ∈ slitPlane) :
    DifferentiableAt ℂ (neumannContourKernel x) z := by
  exact ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (I * (x : ℂ) * z)) z).mul
    ((differentiableAt_const 1).sub differentiableAt_id |>.cpow_const hminus)).mul
    ((differentiableAt_const 1).add differentiableAt_id |>.cpow_const hplus)

theorem norm_neumannContourKernel (x : ℝ) (z : ℂ) :
    ‖neumannContourKernel x z‖ =
      Real.exp (-x * z.im) * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) *
        ‖1 + z‖ ^ (-(1 / 2 : ℝ)) := by
  unfold neumannContourKernel
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have hm := Complex.norm_cpow_real (1 - z) (-(1 / 2 : ℝ))
  have hp := Complex.norm_cpow_real (1 + z) (-(1 / 2 : ℝ))
  norm_num only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at hm hp
  rw [hm, hp]
  congr 2
  simp [mul_re, mul_im]

theorem neumannContourKernel_slit_vertical {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 < t) :
    1 - ((b : ℂ) + t * I) ∈ slitPlane ∧
      1 + ((b : ℂ) + t * I) ∈ slitPlane := by
  constructor
  · apply Or.inr
    simp only [sub_im, one_im, add_im, ofReal_im, mul_im, I_im, ofReal_re,
      I_re, mul_one, mul_zero, add_zero, zero_add, zero_sub]
    exact neg_ne_zero.mpr ht.ne'
  · apply Or.inl
    simp only [add_re, one_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    linarith

theorem norm_neumannContourKernel_vertical_le {x b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 < t) :
    ‖neumannContourKernel x ((b : ℂ) + t * I)‖ ≤
      Real.exp (-x * t) * t ^ (-(1 / 2 : ℝ)) := by
  have hm : t ≤ ‖1 - ((b : ℂ) + t * I)‖ := by
    have h := Complex.abs_im_le_norm (1 - ((b : ℂ) + t * I))
    simpa [abs_of_pos ht] using h
  have hp : 1 ≤ ‖1 + ((b : ℂ) + t * I)‖ := by
    have h := Complex.re_le_norm (1 + ((b : ℂ) + t * I))
    simp only [add_re, one_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self, add_zero] at h
    linarith
  have hmp := Real.rpow_le_rpow_of_nonpos ht hm (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hpp := Real.rpow_le_rpow_of_nonpos zero_lt_one hp (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  rw [Real.one_rpow] at hpp
  rw [norm_neumannContourKernel]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
    add_zero, zero_add]
  calc
    _ ≤ Real.exp (-x * t) * t ^ (-(1 / 2 : ℝ)) * 1 := by gcongr
    _ = _ := mul_one _

theorem norm_neumannContourKernel_horizontal_le {x u H : ℝ} (hH : 1 ≤ H) :
    ‖neumannContourKernel x ((u : ℂ) + H * I)‖ ≤ Real.exp (-x * H) := by
  have hH0 : 0 < H := by linarith
  have hm : 1 ≤ ‖1 - ((u : ℂ) + H * I)‖ := by
    have h := Complex.abs_im_le_norm (1 - ((u : ℂ) + H * I))
    have he : H ≤ ‖1 - ((u : ℂ) + H * I)‖ := by simpa [abs_of_pos hH0] using h
    exact hH.trans he
  have hp : 1 ≤ ‖1 + ((u : ℂ) + H * I)‖ := by
    have h := Complex.abs_im_le_norm (1 + ((u : ℂ) + H * I))
    have he : H ≤ ‖1 + ((u : ℂ) + H * I)‖ := by simpa [abs_of_pos hH0] using h
    exact hH.trans he
  have hmp := Real.rpow_le_rpow_of_nonpos zero_lt_one hm (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hpp := Real.rpow_le_rpow_of_nonpos zero_lt_one hp (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  rw [Real.one_rpow] at hmp hpp
  rw [norm_neumannContourKernel]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
    add_zero, zero_add]
  calc
    _ ≤ Real.exp (-x * H) * 1 * 1 := by gcongr
    _ = _ := by ring

theorem continuousOn_neumannContourKernel_vertical (x : ℝ) {b : ℝ}
    (hb : 0 ≤ b) :
    ContinuousOn (fun t : ℝ => neumannContourKernel x ((b : ℂ) + t * I)) (Ioi 0) := by
  intro t ht
  have hs := neumannContourKernel_slit_vertical hb ht
  exact ((differentiableAt_neumannContourKernel x hs.1 hs.2).continuousAt.comp
    (f := fun t : ℝ => (b : ℂ) + t * I)
    (by fun_prop : ContinuousAt (fun t : ℝ => (b : ℂ) + t * I) t)).continuousWithinAt

theorem integrableOn_neumannContourKernel_vertical {x b : ℝ}
    (hx : 0 < x) (hb : 0 ≤ b) :
    IntegrableOn (fun t : ℝ => neumannContourKernel x ((b : ℂ) + t * I)) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-x * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : -1 < -(1 / 2 : ℝ))
        (by norm_num : 0 < (1 : ℝ)) hx
  apply hi.mono' ((continuousOn_neumannContourKernel_vertical x hb).aestronglyMeasurable
    measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [mul_comm] using norm_neumannContourKernel_vertical_le hb ht

theorem neumannContourKernel_finite_rectangle (x : ℝ) {b H : ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) :
    (∫ u in (0 : ℝ)..b, neumannContourKernel x u) -
      (∫ u in (0 : ℝ)..b, neumannContourKernel x ((u : ℂ) + H * I)) +
      I * (∫ t in (0 : ℝ)..H, neumannContourKernel x ((b : ℂ) + t * I)) -
      I * (∫ t in (0 : ℝ)..H, neumannContourKernel x (t * I)) = 0 := by
  have hd : DifferentiableOn ℂ (neumannContourKernel x)
      (uIcc (0 : ℝ) b ×ℂ uIcc (0 : ℝ) H) := by
    intro z hz
    have hr : z.re ∈ Icc 0 b := by simpa only [uIcc_of_le hb] using! hz.1
    apply (differentiableAt_neumannContourKernel x ?_ ?_).differentiableWithinAt
    · apply Or.inl
      simp only [sub_re, one_re]
      linarith [hr.2]
    · apply Or.inl
      simp only [add_re, one_re]
      linarith [hr.1]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (neumannContourKernel x) 0 ((b : ℂ) + H * I)
    (by simpa using hd)
  simpa using h

end MathCollab.Density.Stronger.Atkinson
