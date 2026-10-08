module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.QuadraticDivisorBand
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


def zetaBandCutoff (a b c d x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / (b - a)) *
    Real.smoothTransition ((d - x) / (d - c))

theorem zetaBandCutoff_nonneg (a b c d x : ℝ) : 0 ≤ zetaBandCutoff a b c d x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem zetaBandCutoff_le_one (a b c d x : ℝ) : zetaBandCutoff a b c d x ≤ 1 := by
  simpa only [one_mul, zetaBandCutoff] using mul_le_mul (Real.smoothTransition.le_one _)
    (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one

theorem contDiff_zetaBandCutoff (a b c d : ℝ) : ContDiff ℝ ∞ (zetaBandCutoff a b c d) :=
  (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem zetaBandCutoff_eq_one {a b c d x : ℝ} (hab : a < b) (hcd : c < d)
    (hbx : b ≤ x) (hxc : x ≤ c) : zetaBandCutoff a b c d x = 1 := by
  unfold zetaBandCutoff
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hcd)).mpr (by linarith)), one_mul]

theorem zetaBandCutoff_eq_zero_left {a b c d x : ℝ} (hab : a < b)
    (hxa : x ≤ a) : zetaBandCutoff a b c d x = 0 := by
  unfold zetaBandCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxa) (sub_pos.mpr hab).le), zero_mul]

theorem zetaBandCutoff_eq_zero_right {a b c d x : ℝ} (hcd : c < d)
    (hdx : d ≤ x) : zetaBandCutoff a b c d x = 0 := by
  unfold zetaBandCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdx) (sub_pos.mpr hcd).le), mul_zero]

theorem support_zetaBandCutoff {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Function.support (zetaBandCutoff a b c d) ⊆ Icc a d := by
  intro x hx
  constructor
  · by_contra h
    exact hx (zetaBandCutoff_eq_zero_left hab (le_of_not_ge h))
  · by_contra h
    exact hx (zetaBandCutoff_eq_zero_right hcd (le_of_not_ge h))

def zetaDivisorBandEdge (T G v : ℝ) : ℝ := T / (2 * Real.pi) * Real.exp (v / G)

def zetaDivisorBandCutoff (T G L : ℝ) : ℝ → ℝ :=
  zetaBandCutoff (zetaDivisorBandEdge T G (-2 * L)) (zetaDivisorBandEdge T G (-L))
    (zetaDivisorBandEdge T G L) (zetaDivisorBandEdge T G (2 * L))

theorem zetaDivisorBandEdge_pos {T : ℝ} (hT : 0 < T) (G v : ℝ) :
    0 < zetaDivisorBandEdge T G v := by unfold zetaDivisorBandEdge; positivity

theorem zetaDivisorBandEdge_strictMono {T G : ℝ} (hT : 0 < T) (hG : 0 < G) :
    StrictMono (zetaDivisorBandEdge T G) := by
  intro v w hvw
  unfold zetaDivisorBandEdge
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hG).mpr hvw))
    (by positivity)

theorem zetaDivisorBandCutoff_eq_one {T G L : ℝ} (hT : 0 < T) (hG : 0 < G)
    (hL : 0 < L) {n : ℕ} (hn : n ∈ zetaQuadraticDivisorBand T G L) :
    zetaDivisorBandCutoff T G L n = 1 := by
  have hm := zetaDivisorBandEdge_strictMono hT hG
  have hb := zetaQuadraticDivisorBand_index_bounds hT hG hn
  exact zetaBandCutoff_eq_one (hm (by linarith)) (hm (by linarith)) hb.1 hb.2

theorem support_zetaDivisorBandCutoff {T G L : ℝ} (hT : 0 < T) (hG : 0 < G)
    (hL : 0 < L) : Function.support (zetaDivisorBandCutoff T G L) ⊆
      Icc (zetaDivisorBandEdge T G (-2 * L)) (zetaDivisorBandEdge T G (2 * L)) := by
  have hm := zetaDivisorBandEdge_strictMono hT hG
  exact support_zetaBandCutoff (hm (by linarith)) (hm (by linarith))

theorem contDiff_zetaDivisorBandCutoff (T G L : ℝ) :
    ContDiff ℝ ∞ (zetaDivisorBandCutoff T G L) := contDiff_zetaBandCutoff _ _ _ _

end MathCollab.Density.Stronger.Atkinson
