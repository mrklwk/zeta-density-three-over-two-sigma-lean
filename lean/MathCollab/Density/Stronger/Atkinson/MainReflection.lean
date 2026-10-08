module
-- Reversible module-visibility port of the audited development.
/-
Native source-interval weighted reflection, using the preserved all-frequency
oscillatory theorem and actual C1 variation. Target pattern from McColm
IntervalAmplitudeBounds.lean, revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0, copyright 2026. Mathlib and existing calculus retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.AllFrequency

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC1Bound.reflection_source {f : ℝ → ℂ} {T M : ℝ}
    (hf : IntervalC1Bound f (T/16) T M) (hT : 0 < T) :
    ‖∫ x in (T/16)..T, f x*((x:ℂ)⁻¹ *
      Complex.exp (((T*Real.log x-2*Real.pi*x:ℝ):ℂ)*I))‖ ≤
        48*M/Real.sqrt T := by
  let a := T/16
  let K : ℝ → ℂ := fun x => ((max a x : ℝ):ℂ)⁻¹ *
    Complex.exp (((T*Real.log (max a x)-2*Real.pi*(max a x):ℝ):ℂ)*I)
  have ha : 0<a := by dsimp [a]; positivity
  have hpos (x : ℝ) : 0 < max a x := ha.trans_le (le_max_left _ _)
  have hmax : Continuous (fun x : ℝ => max a x) := by fun_prop
  have hlog : Continuous (fun x : ℝ => Real.log (max a x)) := hmax.log (fun x => (hpos x).ne')
  have hK : Continuous K := by
    have hi : Continuous (fun x : ℝ => ((max a x:ℝ):ℂ)⁻¹) :=
      (Complex.continuous_ofReal.comp hmax).inv₀ (fun x => Complex.ofReal_ne_zero.mpr (hpos x).ne')
    exact hi.mul (Complex.continuous_exp.comp (by fun_prop))
  have hKeq (x : ℝ) (hx : a≤x) : K x = (x:ℂ)⁻¹ *
      Complex.exp (((T*Real.log x-2*Real.pi*x:ℝ):ℂ)*I) := by simp only [K, max_eq_right hx]
  have hp (x : ℝ) (hx : x∈Icc a T) :
      ‖∫ y in a..x, K y‖ ≤ 6/Real.sqrt (2*Real.pi*a) := by
    have he : (∫ y in a..x, K y) = MathCollab.Density.gmReflectionIntegral T a x := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hx.1] at hy
      exact hKeq y hy.1
    rw [he]
    exact MathCollab.Density.norm_gmReflectionIntegral_le_six_div_sqrt ha hx.1
  have h := hf.continuousKernel_of_primitive_bound hK (by linarith) hp
  have he : (∫ x in (T/16)..T, f x*K x) = ∫ x in (T/16)..T,
      f x*((x:ℂ)⁻¹*Complex.exp (((T*Real.log x-2*Real.pi*x:ℝ):ℂ)*I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : T/16≤T)] at hx
    exact congrArg (fun z : ℂ => f x*z) (hKeq x hx.1)
  rw [he] at h
  have hd : 0<Real.sqrt (2*Real.pi*a) := Real.sqrt_pos.mpr (by positivity)
  have ht : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  have hs : Real.sqrt T ≤ 4*Real.sqrt (2*Real.pi*a) := by
    have hsq := Real.sq_sqrt (show 0≤2*Real.pi*a by positivity)
    have hsqT := Real.sq_sqrt hT.le
    dsimp [a] at hsq
    nlinarith [Real.pi_gt_three, Real.sqrt_nonneg (2*Real.pi*a)]
  apply h.trans
  have heq : 2*(6/Real.sqrt (2*Real.pi*a))*M = 12*M/Real.sqrt (2*Real.pi*a) := by ring
  rw [heq]
  apply (div_le_div_iff₀ hd ht).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hf.nonneg]

end MathCollab.Density.Stronger.Atkinson
