module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootFirstDerivative

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform integral bound through the actual saddle

Two nonstationary tails and a length-two central interval give one
bound for every positive interval and every real carrier parameter.
The divisor frequency and its sign do not enter the bound.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonRootKernel (T b y : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (atkinsonRootPhase T b y : ℂ))

theorem norm_atkinsonRootKernel (T b y : ℝ) : ‖atkinsonRootKernel T b y‖ = 1 := by
  simp [atkinsonRootKernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem continuousAt_atkinsonRootKernel (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (atkinsonRootKernel T b) y := by
  have h := (hasDerivAt_atkinsonRootPhase T b hy).continuousAt
  unfold atkinsonRootKernel
  fun_prop

theorem intervalIntegrable_atkinsonRootKernel (T b : ℝ) {a c : ℝ}
    (ha : 0 < a) (hac : a ≤ c) :
    IntervalIntegrable (atkinsonRootKernel T b) volume a c := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hac]
  exact fun y hy => (continuousAt_atkinsonRootKernel T b (ha.trans_le hy.1)).continuousWithinAt

theorem norm_atkinsonRootKernel_integral_le_length (T b : ℝ) {a c : ℝ} (hac : a ≤ c) :
    ‖∫ y in a..c, atkinsonRootKernel T b y‖ ≤ c - a := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := c) (fun y _ => (norm_atkinsonRootKernel T b y).le)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hac), one_mul] using h

theorem norm_atkinsonRootKernel_integral_le_four {T : ℝ} (hT : 0 < T)
    (b : ℝ) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    ‖∫ y in a..c, atkinsonRootKernel T b y‖ ≤ 4 := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  have hsmall : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity : 0 < 2 * Real.pi)).2
    linarith [Real.pi_gt_three]
  by_cases hleft : c ≤ r - 1
  · exact (norm_atkinsonRootPhase_integral_left hT ha hac hleft).trans (by linarith)
  by_cases hright : r + 1 ≤ a
  · exact (norm_atkinsonRootPhase_integral_right hT ha hac hright).trans (by linarith)
  let u := max a (r - 1)
  let v := min c (r + 1)
  have hau : a ≤ u := le_max_left _ _
  have huc : u ≤ c := max_le hac (by linarith)
  have hav : a ≤ v := le_min hac (by linarith)
  have hvc : v ≤ c := min_le_left _ _
  have huv : u ≤ v := by
    apply max_le
    · exact hav
    · exact le_min (by linarith) (by linarith)
  have hu0 : 0 < u := ha.trans_le hau
  have hv0 : 0 < v := ha.trans_le hav
  have hlow : ‖∫ y in a..u, atkinsonRootKernel T b y‖ ≤ 1 := by
    rcases le_total (r - 1) a with hr | hr
    · have hu : u = a := max_eq_left hr
      simp [hu]
    · have hu : u = r - 1 := max_eq_right hr
      exact (norm_atkinsonRootPhase_integral_left hT ha hau (by rw [hu])).trans hsmall
  have hhigh : ‖∫ y in v..c, atkinsonRootKernel T b y‖ ≤ 1 := by
    rcases le_total c (r + 1) with hr | hr
    · have hv : v = c := min_eq_left hr
      simp [hv]
    · have hv : v = r + 1 := min_eq_right hr
      exact (norm_atkinsonRootPhase_integral_right hT hv0 hvc (by rw [hv])).trans hsmall
  have hmid : ‖∫ y in u..v, atkinsonRootKernel T b y‖ ≤ 2 := by
    apply (norm_atkinsonRootKernel_integral_le_length T b huv).trans
    have hru : r - 1 ≤ u := le_max_right _ _
    have hvr : v ≤ r + 1 := min_le_right _ _
    linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_atkinsonRootKernel T b ha hau)
    (intervalIntegrable_atkinsonRootKernel T b hu0 huc)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_atkinsonRootKernel T b hu0 huv)
    (intervalIntegrable_atkinsonRootKernel T b hv0 hvc)]
  exact (norm_add_le _ _).trans (by
    have h := norm_add_le (∫ y in u..v, atkinsonRootKernel T b y)
      (∫ y in v..c, atkinsonRootKernel T b y)
    linarith)

end MathCollab.Density.Stronger.Atkinson
