module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightFreezing

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
/-- The actual zeta square is approximated by the complete frozen
oscillatory source on the closed half-height window. -/
theorem exists_abs_zetaSquareNorm_sub_frozen_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 8 ≤ T → ∀ x : ℝ, |x| ≤ T / 2 →
      |zetaMomentCriticalNorm (T + x) ^ 2 - 2 * (zetaSquareFrozenDivisorIntegral T x).re| ≤
        C * (1 + |x| * T ^ (-1 / 2 + ε)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSquareSource_sub_frozen_le ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro T hT x hx
  rw [zetaSquareNorm_eq_reflected_source, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ‖zetaSquareDivisorIntegral (-(T + x)) / zetaSquareGammaNormalization (T + x) -
        zetaSquareFrozenDivisorIntegral T x‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm
        (zetaSquareDivisorIntegral (-(T + x)) / zetaSquareGammaNormalization (T + x) -
          zetaSquareFrozenDivisorIntegral T x)
    _ ≤ 2 * (C * (1 + |x| * T ^ (-1 / 2 + ε))) :=
      mul_le_mul_of_nonneg_left (hbound T hT x hx) (by norm_num)
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
