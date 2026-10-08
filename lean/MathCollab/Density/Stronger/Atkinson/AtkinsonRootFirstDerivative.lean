module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootPhase
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_atkinsonRootPhase_integral_right {T b a c : ℝ}
    (hT : 0 < T) (ha : 0 < a) (hac : a ≤ c)
    (hr : atkinsonSaddleRoot (T / (2 * Real.pi)) b + 1 ≤ a) :
    ‖∫ y in a..c, Complex.exp (2 * Real.pi * I * (atkinsonRootPhase T b y : ℂ))‖ ≤
      1 / (2 * Real.pi) := by
  have hd (y : ℝ) (hy : y ∈ Icc a c) :
      deriv (atkinsonRootPhase T b) y = atkinsonRootSlope T b y :=
    (hasDerivAt_atkinsonRootPhase T b (ha.trans_le hy.1)).deriv
  apply norm_phaseIntegral_le_of_negative_slope hac (by norm_num : (0 : ℝ) < 2)
    (fun y hy => contDiffAt_atkinsonRootPhase T b (ha.trans_le hy.1))
  · intro y hy
    rw [hd y hy]
    exact atkinsonRootSlope_le_neg_two hT (ha.trans_le hy.1) (hr.trans hy.1)
  · intro x hx y hy hxy
    rw [hd x hx, hd y hy]
    exact (atkinsonRootSlope_strictAnti hT.le b).antitoneOn
      (ha.trans_le hx.1) (ha.trans_le hy.1) hxy

theorem norm_atkinsonRootPhase_integral_left {T b a c : ℝ}
    (hT : 0 < T) (ha : 0 < a) (hac : a ≤ c)
    (hr : c ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - 1) :
    ‖∫ y in a..c, Complex.exp (2 * Real.pi * I * (atkinsonRootPhase T b y : ℂ))‖ ≤
      1 / (2 * Real.pi) := by
  have hd (y : ℝ) (hy : y ∈ Icc a c) :
      deriv (atkinsonRootPhase T b) y = atkinsonRootSlope T b y :=
    (hasDerivAt_atkinsonRootPhase T b (ha.trans_le hy.1)).deriv
  apply norm_phaseIntegral_le_of_positive_slope hac (by norm_num : (0 : ℝ) < 2)
    (fun y hy => contDiffAt_atkinsonRootPhase T b (ha.trans_le hy.1))
  · intro y hy
    rw [hd y hy]
    exact two_le_atkinsonRootSlope hT (ha.trans_le hy.1) (hy.2.trans hr)
  · intro x hx y hy hxy
    rw [hd x hx, hd y hy]
    exact (atkinsonRootSlope_strictAnti hT.le b).antitoneOn
      (ha.trans_le hx.1) (ha.trans_le hy.1) hxy

end MathCollab.Density.Stronger.Atkinson
