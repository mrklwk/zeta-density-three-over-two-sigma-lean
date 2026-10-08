module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice from ZetaMainElementaryWeights.lean,
revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain
Apache-2.0 attribution. No Voronoi identity or analytic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem intervalC1Bound_source_sqrt {T : ℝ} (hT : 0 < T) :
    IntervalC1Bound (fun x : ℝ => (Real.sqrt x : ℂ)) (T / 16) T (Real.sqrt T) := by
  apply intervalC1Bound_ofReal_of_deriv_nonneg (by linarith) (Real.sqrt_nonneg T)
  · intro x hx
    exact Real.contDiffAt_sqrt (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < T / 16) hx.1))
  · intro x hx
    exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hx.2⟩
  · intro x hx
    exact Real.sqrt_monotone.deriv_nonneg

theorem mul_exp_neg_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    x * Real.exp (-Real.log x / 2) = Real.sqrt x := by
  calc
    _ = Real.exp (Real.log x + (-Real.log x / 2)) := by rw [Real.exp_add, Real.exp_log hx]
    _ = x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hx]
      congr 1
      ring
    _ = _ := by rw [Real.sqrt_eq_rpow]


theorem intervalC1Bound_source_log {T : ℝ} (hT : 16 ≤ T) :
    IntervalC1Bound (fun x : ℝ => ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ))
      (T / 16) T (Real.log T + 2 * Real.eulerMascheroniConstant) := by
  have hγ : 0 ≤ Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  apply intervalC1Bound_ofReal_of_deriv_nonneg (by linarith)
    (by positivity [Real.log_nonneg (show 1 ≤ T by linarith)])
  · intro x hx
    exact (Real.contDiffAt_log.mpr (ne_of_gt (by linarith [hx.1] : 0 < x))).add contDiffAt_const
  · intro x hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    exact ⟨by positivity [Real.log_nonneg hx1],
      by linarith [Real.log_le_log (by linarith : 0 < x) hx.2]⟩
  · intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [((Real.hasDerivAt_log hx0.ne').add_const
      (2 * Real.eulerMascheroniConstant)).deriv]
    positivity

theorem sourceLogWeight_le_three_log {T : ℝ} (hlog : 1 ≤ Real.log T) :
    Real.log T + 2 * Real.eulerMascheroniConstant ≤ 3 * Real.log T := by
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

end MathCollab.Density.Stronger.Atkinson
