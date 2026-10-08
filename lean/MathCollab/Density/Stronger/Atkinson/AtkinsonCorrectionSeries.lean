module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction; see third_party/twelfth/ATKINSON_CORRECTION_SERIES_MANIFEST.json.
Mathlib and the nonstationary foundations retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCorrectionBounds
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCarrierIntegrals

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonCorrectionSum (T G L : ℝ) : ℂ := ∑' n : ℕ, atkinsonCorrectionTerm T G L n

theorem atkinsonTwoTermCarrierIntegral_eq_leading_sub_correction (T G L : ℝ) (n : ℕ) :
    atkinsonTwoTermCarrierIntegral T G L n =
      atkinsonLeadingIntegral T G L n - atkinsonCorrectionIntegral T G L n := by
  unfold atkinsonTwoTermCarrierIntegral atkinsonLeadingIntegral atkinsonCorrectionIntegral
  ring

theorem zetaAtkinsonTwoTerm_eq_leading_sub_correction {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (n : ℕ) :
    zetaAtkinsonTwoTerm T G L n = atkinsonLeadingTerm T G L n - atkinsonCorrectionTerm T G L n := by
  rw [zetaAtkinsonTwoTerm_eq_carrierIntegral hT hG hL hwidth,
    atkinsonTwoTermCarrierIntegral_eq_leading_sub_correction]
  unfold atkinsonLeadingTerm atkinsonCorrectionTerm
  ring

theorem summable_atkinsonCorrectionTerm {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (atkinsonCorrectionTerm T G L) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_atkinsonCorrectionTerm_le
  exact Summable.of_norm_bounded
    ((summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm.mul_left (C * G))
    (hbound T G L hT hG hGT hL hwidth)

theorem exists_norm_atkinsonCorrectionSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ‖atkinsonCorrectionSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonCorrectionTerm_le
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (5 / 4) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs := summable_atkinsonCorrectionTerm hT hG hGT hL hwidth
  have hd := (summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖atkinsonCorrectionTerm T G L n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (C * G) * ‖divisorDirichletTerm (5 / 4) n‖ :=
      hs.norm.tsum_le_tsum (hbound T G L hT hG hGT hL hwidth) (hd.mul_left _)
    _ = C * G * S := tsum_mul_left
    _ ≤ _ := by nlinarith

end MathCollab.Density.Stronger.Atkinson
