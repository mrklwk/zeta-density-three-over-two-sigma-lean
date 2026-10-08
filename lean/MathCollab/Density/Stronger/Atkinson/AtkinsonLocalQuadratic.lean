module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.AtkinsonQuadraticKernel
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryTails

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC2Bound.atkinsonLocalQuadratic {f : ℝ → ℂ} {a c M R T H : ℝ}
    (hf : IntervalC2Bound f a c M R) (hT : 0 < T) (b : ℝ) (hH : 0 ≤ H)
    (hleft : a ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)
    (hright : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ c)
    (hwindow : H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    ‖(∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), f y * atkinsonRootKernel T b y) -
      f (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
      M * (2 * R * H ^ 2 + 8 * T * H ^ 4 /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have horder : r - H ≤ r + H := by linarith
  have hpositive : 0 < r - H := by change H ≤ r / 2 at hwindow; linarith
  have hmem {y : ℝ} (hy : y ∈ Icc (r - H) (r + H)) : y ∈ Icc a c :=
    ⟨hleft.trans hy.1, hy.2.trans hright⟩
  have hrmem : r ∈ Icc a c := hmem ⟨by linarith, by linarith⟩
  have hfcont : ContinuousOn f (uIcc (r - H) (r + H)) := by
    rw [uIcc_of_le horder]
    exact fun y hy => (hf.smooth y (hmem hy)).continuousAt.continuousWithinAt
  have hactual : IntervalIntegrable (fun y => f y * atkinsonRootKernel T b y)
      volume (r - H) (r + H) :=
    hfcont.intervalIntegrable.mul_continuousOn (by
      rw [uIcc_of_le horder]
      exact fun y hy => (continuousAt_atkinsonRootKernel T b
        (hpositive.trans_le hy.1)).continuousWithinAt)
  have hquad := (continuous_atkinsonRootQuadraticKernel T b).intervalIntegrable
    (μ := volume) (a := r - H) (b := r + H)
  have hpoint (y : ℝ) (hy : y ∈ Icc (r - H) (r + H)) :
      ‖f y * atkinsonRootKernel T b y - f r * atkinsonRootQuadraticKernel T b y‖ ≤
        M * R * H + M * (4 * T * H ^ 3 / r ^ 3) := by
    have hyH : |y - r| ≤ H := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hvar : ‖f y - f r‖ ≤ M * R * H :=
      (hf.norm_sub_le hrmem (hmem hy)).trans
        (mul_le_mul_of_nonneg_left hyH (mul_nonneg hf.nonneg hf.scale_nonneg))
    have hphase : ‖atkinsonRootKernel T b y - atkinsonRootQuadraticKernel T b y‖ ≤
        4 * T * H ^ 3 / r ^ 3 := by
      apply (norm_atkinsonRootKernel_sub_quadratic_le hT b (hyH.trans hwindow)).trans
      change 4 * T * |y - r| ^ 3 / r ^ 3 ≤ _
      gcongr
    have he : f y * atkinsonRootKernel T b y - f r * atkinsonRootQuadraticKernel T b y =
        (f y - f r) * atkinsonRootKernel T b y +
          f r * (atkinsonRootKernel T b y - atkinsonRootQuadraticKernel T b y) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_atkinsonRootKernel, mul_one, norm_mul]
    exact add_le_add hvar (mul_le_mul (hf.norm_le r hrmem) hphase (norm_nonneg _) hf.nonneg)
  change ‖(∫ y in (r - H)..(r + H), f y * atkinsonRootKernel T b y) -
    f r * ∫ y in (r - H)..(r + H), atkinsonRootQuadraticKernel T b y‖ ≤ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hactual
    (hquad.const_mul (f r))]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r - H) (b := r + H) (fun y hy => hpoint y (by
      rw [uIoc_of_le horder] at hy
      exact ⟨hy.1.le, hy.2⟩))
  apply hbound.trans_eq
  rw [abs_of_nonneg (by linarith : 0 ≤ r + H - (r - H))]
  ring

theorem IntervalC2Bound.atkinsonQuadraticApproximation {f : ℝ → ℂ}
    {a c M R T H : ℝ} (hf : IntervalC2Bound f a c M R)
    (hv : IntervalC1Bound f a c M) (hT : 0 < T) (b : ℝ)
    (ha : 0 < a) (hH : 0 < H)
    (hleft : a ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)
    (hright : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ c)
    (hwindow : H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    ‖(∫ y in a..c, f y * atkinsonRootKernel T b y) -
      f (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
      M * (2 / (H * Real.pi) + 2 * R * H ^ 2 + 8 * T * H ^ 4 /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  have hlocal := hf.atkinsonLocalQuadratic hT b hH.le hleft hright hwindow
  have htail := hv.atkinsonRoot_sub_local hT b ha hH hleft hright
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add htail hlocal).trans_eq ?_)
  ring


end MathCollab.Density.Stronger.Atkinson
