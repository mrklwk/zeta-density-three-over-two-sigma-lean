module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform tails with positive Gaussian damping

The reciprocal-slope estimate is uniform down to zero damping.
Only strictly positive damping is used for whole-line integrability later.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

def fresnelDampedKernel (ε c x : ℝ) : ℂ :=
  Complex.exp (-((ε : ℂ) + 2 * Real.pi * c * I) * (x : ℂ) ^ 2)

theorem continuous_fresnelDampedKernel (ε c : ℝ) : Continuous (fresnelDampedKernel ε c) := by
  unfold fresnelDampedKernel
  fun_prop

theorem fresnelDampedKernel_eq_weighted (ε c x : ℝ) :
    fresnelDampedKernel ε c x = (Real.exp (-ε * x ^ 2) : ℂ) *
      Complex.exp (2 * Real.pi * I * ((-c * x ^ 2 : ℝ) : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  unfold fresnelDampedKernel
  congr 1
  push_cast
  ring

theorem norm_fresnelDampedKernel {ε : ℝ} (hε : 0 ≤ ε) (c x : ℝ) :
    ‖fresnelDampedKernel ε c x‖ ≤ 1 := by
  have hphase : ‖Complex.exp (2 * Real.pi * I * ((-c * x ^ 2 : ℝ) : ℂ))‖ = 1 := by
    have hn (v : ℝ) : ‖Complex.exp ((v : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp]
    rw [show 2 * Real.pi * I * ((-c * x ^ 2 : ℝ) : ℂ) =
      (((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ) * I) by push_cast; ring]
    exact hn _
  rw [fresnelDampedKernel_eq_weighted, norm_mul, hphase, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg hε (sq_nonneg x)]

theorem fresnelDampedKernel_neg (ε c x : ℝ) :
    fresnelDampedKernel ε c (-x) = fresnelDampedKernel ε c x := by
  simp only [fresnelDampedKernel, Complex.ofReal_neg, neg_sq]

theorem intervalC1Bound_gaussian_damping {ε a b : ℝ}
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalC1Bound (fun x => (Real.exp (-ε * x ^ 2) : ℂ)) a b 1 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-ε * y ^ 2))
      (Real.exp (-ε * x ^ 2) * (-2 * ε * x)) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (-ε)).exp using 1 <;> dsimp [id]
    ring
  apply intervalC1Bound_ofReal_of_deriv_nonpos hab (by norm_num) (by intros; fun_prop)
  · intro x _
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    nlinarith [mul_nonneg hε (sq_nonneg x)]
  · intro x hx
    rw [(hd x).deriv]
    have hx0 : 0 ≤ x := ha.trans hx.1
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by nlinarith [mul_nonneg hε hx0])

theorem norm_fresnelPhase_integral_le {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (2 * Real.pi * I * ((-c * x ^ 2 : ℝ) : ℂ))‖ ≤
      1 / (2 * c * a * Real.pi) := by
  have hd (x : ℝ) : deriv (fun y : ℝ => -c * y ^ 2) x = -2 * c * x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (-c)).deriv using 1 <;> dsimp [id]
    ring
  apply norm_phaseIntegral_le_of_negative_slope hab (by positivity : 0 < 2 * c * a)
    (by intros; fun_prop)
  · intro x hx
    rw [hd x]
    nlinarith [mul_le_mul_of_nonneg_left hx.1 hc.le]
  · intro x _ y _ hxy
    rw [hd x, hd y]
    nlinarith [mul_le_mul_of_nonneg_left hxy hc.le]

theorem norm_integral_fresnelDampedKernel_le {ε c a b : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, fresnelDampedKernel ε c x‖ ≤ 1 / (c * a * Real.pi) := by
  have h := (intervalC1Bound_gaussian_damping hε ha.le hab).continuousKernel_of_primitive_bound
    (K := fun x => Complex.exp (2 * Real.pi * I * ((-c * x ^ 2 : ℝ) : ℂ)))
    (by fun_prop) hab (fun x hx => norm_fresnelPhase_integral_le hc ha hx.1)
  simp_rw [fresnelDampedKernel_eq_weighted]
  apply h.trans_eq
  ring

end MathCollab.Density.Stronger.Atkinson
