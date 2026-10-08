module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction; see third_party/twelfth/ATKINSON_CORRECTION_SERIES_MANIFEST.json.
Mathlib and the nonstationary foundations retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_norm_atkinsonPowerPair_le (α : ℝ) (c d : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
      ‖c * atkinsonPowerIntegral T G L α b + d * atkinsonPowerIntegral T G L α (-b)‖ ≤
        C * G * T ^ (-α) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonPowerIntegral_le α
  refine ⟨(1 + ‖c‖ + ‖d‖) * C, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * (C * G * T ^ (-α)) + ‖d‖ * (C * G * T ^ (-α)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hbound T G L b hT hG hGT hL hwidth) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hbound T G L (-b) hT hG hGT hL hwidth) (norm_nonneg _))
    _ ≤ _ := by
      have hb : 0 ≤ C * G * T ^ (-α) := by positivity
      nlinarith

end MathCollab.Density.Stronger.Atkinson
