module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ReciprocalSecondDerivativeBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Two integrations by parts for the actual root phase

The first integration differentiates the quotient by the true slope.
The second uses the proved primitive bound. Endpoint vanishing is explicit.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem hasDerivAt_atkinsonRootKernel (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (atkinsonRootKernel T b)
      ((((2 * Real.pi : ℝ) : ℂ) * I) * (atkinsonRootSlope T b y : ℂ) *
        atkinsonRootKernel T b y) y := by
  have h := (((hasDerivAt_atkinsonRootPhase T b hy).ofReal_comp).const_mul
    (2 * Real.pi * I)).cexp
  convert h using 1
  · unfold atkinsonRootKernel
    ring
  · unfold atkinsonRootKernel
    push_cast
    ring

theorem IntervalC2Bound.atkinsonRoot_secondOrder {f : ℝ → ℂ} {T b a c M R B : ℝ}
    (hw : IntervalC2Bound
      (fun y => f y * (((atkinsonRootSlope T b y)⁻¹ : ℝ) : ℂ)) a c M R)
    (ha : 0 < a) (hac : a ≤ c)
    (hne : ∀ y ∈ Icc a c, atkinsonRootSlope T b y ≠ 0)
    (hfa : f a = 0) (hfc : f c = 0)
    (hprimitive : ∀ x ∈ Icc a c, ‖∫ y in a..x, atkinsonRootKernel T b y‖ ≤ B) :
    ‖∫ y in a..c, f y * atkinsonRootKernel T b y‖ ≤
      B * M * (R + (c - a) * R ^ 2) / Real.pi := by
  let w : ℝ → ℂ := fun y => f y * (((atkinsonRootSlope T b y)⁻¹ : ℝ) : ℂ)
  let k : ℂ := ((2 * Real.pi : ℝ) : ℂ) * I
  have hdi : IntervalIntegrable (deriv w) volume a c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hac]
    exact fun x hx => ((hw.smooth x hx).derivWithin (m := 1)
      (by norm_num)).continuousAt.continuousWithinAt
  have hki : IntervalIntegrable
      (fun y => k * (atkinsonRootSlope T b y : ℂ) * atkinsonRootKernel T b y) volume a c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hac]
    intro y hy
    have hys := (hasDerivAt_atkinsonRootSlope T b (ha.trans_le hy.1)).continuousAt
    have hyk := continuousAt_atkinsonRootKernel T b (ha.trans_le hy.1)
    exact ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hys)).mul
      hyk).continuousWithinAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := w) (u' := deriv w) (v := atkinsonRootKernel T b)
    (v' := fun y => k * (atkinsonRootSlope T b y : ℂ) * atkinsonRootKernel T b y)
    (fun y hy => by
      rw [uIcc_of_le hac] at hy
      exact ((hw.smooth y hy).differentiableAt (by norm_num)).hasDerivAt)
    (fun y hy => by
      rw [uIcc_of_le hac] at hy
      exact hasDerivAt_atkinsonRootKernel T b (ha.trans_le hy.1)) hdi hki
  have hwa : w a = 0 := by simp only [w, hfa, zero_mul]
  have hwc : w c = 0 := by simp only [w, hfc, zero_mul]
  have he : (∫ y in a..c,
      w y * (k * (atkinsonRootSlope T b y : ℂ) * atkinsonRootKernel T b y)) =
        k * ∫ y in a..c, f y * atkinsonRootKernel T b y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hac] at hy
    calc
      _ = k * (f y * atkinsonRootKernel T b y) *
          ((((atkinsonRootSlope T b y)⁻¹ : ℝ) : ℂ) * (atkinsonRootSlope T b y : ℂ)) := by
        dsimp only [w]
        ring
      _ = _ := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hne y hy), Complex.ofReal_one, mul_one]
  rw [he, hwa, hwc, zero_mul, zero_mul, sub_self, zero_sub] at hparts
  have hnorm := congrArg norm hparts
  have hk : ‖k‖ = 2 * Real.pi := by
    dsimp only [k]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), Complex.norm_I, mul_one]
  rw [norm_mul, hk, norm_neg] at hnorm
  have hd := (hw.deriv_c1 hac).atkinsonRoot_of_primitive_bound b ha hac hprimitive
  apply (le_div_iff₀ Real.pi_pos).2
  change ‖∫ y in a..c, deriv w y * atkinsonRootKernel T b y‖ ≤ _ at hd
  nlinarith

end MathCollab.Density.Stronger.Atkinson
