module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootIntegral
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual variation under square coordinates and oscillatory integration

The square change of variables preserves the derivative-norm integral.
The weighted carrier bound consumes a concrete C1 amplitude and the
proved frequency-uniform root-kernel estimate.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC1Bound.comp_sq {f : ℝ → ℂ} {a c M : ℝ}
    (hf : IntervalC1Bound f (a ^ 2) (c ^ 2) M) (ha : 0 ≤ a) (hac : a ≤ c) :
    IntervalC1Bound (fun y => f (y ^ 2)) a c M := by
  have hmem (y : ℝ) (hy : y ∈ Icc a c) : y ^ 2 ∈ Icc (a ^ 2) (c ^ 2) := by
    constructor <;> nlinarith [hy.1, hy.2]
  have hd (y : ℝ) (hy : y ∈ Icc a c) :
      deriv (fun z => f (z ^ 2)) y = (2 * y) • deriv f (y ^ 2) := by
    have h := (((hf.smooth (y ^ 2) (hmem y hy)).differentiableAt
      (by norm_num)).hasDerivAt.scomp (h := fun z : ℝ => z ^ 2)
        y ((hasDerivAt_id y).pow 2)).deriv
    simpa using! h
  refine ⟨hf.nonneg, fun y hy => (hf.smooth (y ^ 2) (hmem y hy)).comp
    (f := fun z : ℝ => z ^ 2) y (by fun_prop),
    fun y hy => hf.norm_le (y ^ 2) (hmem y hy), ?_⟩
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun y : ℝ => y ^ 2) (f' := fun y : ℝ => 2 * y)
    (g := fun x => ‖deriv f x‖) (a := a) (b := c)
    (by fun_prop) (fun y _ => by simpa using! (hasDerivAt_id y).pow 2)
    (fun y hy => by
      rw [min_eq_left hac, max_eq_right hac] at hy
      linarith [hy.1])
  have heq : (∫ y in a..c, ‖deriv (fun z => f (z ^ 2)) y‖) =
      ∫ y in a..c, (fun x => ‖deriv f x‖) (y ^ 2) * (2 * y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hac] at hy
    dsimp only
    rw [hd y hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hy.1] : 0 ≤ 2 * y)]
    exact mul_comm _ _
  dsimp only [Function.comp_apply] at he
  rw [heq, he]
  exact hf.variation_le

theorem IntervalC1Bound.atkinsonRoot_of_primitive_bound {f : ℝ → ℂ} {a c M T B : ℝ}
    (hf : IntervalC1Bound f a c M) (b : ℝ) (ha : 0 < a) (hac : a ≤ c)
    (hprimitive : ∀ x ∈ Icc a c, ‖∫ y in a..x, atkinsonRootKernel T b y‖ ≤ B) :
    ‖∫ y in a..c, f y * atkinsonRootKernel T b y‖ ≤ 2 * B * M := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hprimitive a ⟨le_rfl, hac⟩)
  let F : ℝ → ℂ := fun x => ∫ y in a..x, atkinsonRootKernel T b y
  have hk : ContinuousOn (atkinsonRootKernel T b) (Ioi 0) :=
    fun x hx => (continuousAt_atkinsonRootKernel T b hx).continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ Icc a c) :
      HasDerivAt F (atkinsonRootKernel T b x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_atkinsonRootKernel T b ha hx.1)
      (hk.stronglyMeasurableAtFilter isOpen_Ioi x (ha.trans_le hx.1))
      (continuousAt_atkinsonRootKernel T b (ha.trans_le hx.1))
  have hF : ContinuousOn F (uIcc a c) := by
    rw [uIcc_of_le hac]
    exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hFb (x : ℝ) (hx : x ∈ Icc a c) : ‖F x‖ ≤ B := hprimitive x hx
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := deriv f) (v := F) (v' := atkinsonRootKernel T b)
    (fun x hx => by
      rw [uIcc_of_le hac] at hx
      exact ((hf.smooth x hx).differentiableAt (by norm_num)).hasDerivAt)
    (fun x hx => by rw [uIcc_of_le hac] at hx; exact hd x hx)
    (hf.derivative_integrable hac) (intervalIntegrable_atkinsonRootKernel T b ha hac)
  have hFA : F a = 0 := by simp [F]
  have hvar : ‖∫ y in a..c, deriv f y * F y‖ ≤ B * M := by
    calc
      _ ≤ |∫ y in a..c, ‖deriv f y * F y‖| := intervalIntegral.norm_integral_le_abs_integral_norm
      _ = ∫ y in a..c, ‖deriv f y * F y‖ := by
        rw [abs_of_nonneg (intervalIntegral.integral_nonneg hac (fun _ _ => norm_nonneg _))]
      _ ≤ ∫ y in a..c, ‖deriv f y‖ * B := by
        apply intervalIntegral.integral_mono_on hac
        · simpa only [norm_mul] using
            (hf.derivative_integrable hac).norm.mul_continuousOn hF.norm
        · exact (hf.derivative_integrable hac).norm.mul_const B
        · intro y hy
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hFb y hy) (norm_nonneg _)
      _ = (∫ y in a..c, ‖deriv f y‖) * B := by rw [intervalIntegral.integral_mul_const]
      _ ≤ B * M := by nlinarith [hf.variation_le]
  rw [hparts, hFA, mul_zero, sub_zero]
  apply (norm_sub_le _ _).trans
  have hprod : ‖f c * F c‖ ≤ M * B := by
    rw [norm_mul]
    exact mul_le_mul (hf.norm_le c ⟨hac, le_rfl⟩) (hFb c ⟨hac, le_rfl⟩)
      (norm_nonneg _) hf.nonneg
  linarith

theorem IntervalC1Bound.atkinsonRoot {f : ℝ → ℂ} {a c M T : ℝ}
    (hf : IntervalC1Bound f a c M) (hT : 0 < T) (b : ℝ)
    (ha : 0 < a) (hac : a ≤ c) :
    ‖∫ y in a..c, f y * atkinsonRootKernel T b y‖ ≤ 8 * M := by
  have h := hf.atkinsonRoot_of_primitive_bound (B := 4) b ha hac
    (fun x hx => norm_atkinsonRootKernel_integral_le_four hT b ha hx.1)
  simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using h

end MathCollab.Density.Stronger.Atkinson
