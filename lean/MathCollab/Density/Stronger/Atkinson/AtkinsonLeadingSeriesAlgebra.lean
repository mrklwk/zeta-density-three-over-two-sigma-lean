module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Adapted from AtkinsonLeadingSeries at exact source revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_LEADING_CONVERGENCE_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCorrectionSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson

/-- With the literal correction already proved summable, convergence of either
actual source series is equivalent to convergence of the other. -/
theorem summable_atkinsonLeadingTerm_iff_twoTerm {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (atkinsonLeadingTerm T G L) ↔ Summable (zetaAtkinsonTwoTerm T G L) := by
  have hc := summable_atkinsonCorrectionTerm hT hG hGT hL hwidth
  have he := zetaAtkinsonTwoTerm_eq_leading_sub_correction (by linarith : 0 < T)
    hG hL hwidth
  constructor
  · intro hs
    exact (hs.sub hc).congr (fun n => (he n).symm)
  · intro hs
    apply (hs.add hc).congr
    intro n
    rw [he n]
    ring

/-- Whole-series subtraction is used only after leading convergence is supplied.
The physical band producer discharges this premise in the companion module. -/
theorem tsum_zetaAtkinsonTwoTerm_eq_leading_sub_correction_of_summable {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hs : Summable (atkinsonLeadingTerm T G L)) :
    (∑' n : ℕ, zetaAtkinsonTwoTerm T G L n) =
      atkinsonLeadingSum T G L - atkinsonCorrectionSum T G L := by
  unfold atkinsonLeadingSum atkinsonCorrectionSum
  simp_rw [zetaAtkinsonTwoTerm_eq_leading_sub_correction (by linarith : 0 < T)
    hG hL hwidth]
  exact hs.tsum_sub (summable_atkinsonCorrectionTerm hT hG hGT hL hwidth)

/-- The constant is uniform before all scales and the explicit convergence premise. -/
theorem exists_norm_tsum_zetaAtkinsonTwoTerm_sub_leading_le_of_summable :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → Summable (atkinsonLeadingTerm T G L) →
        ‖(∑' n : ℕ, zetaAtkinsonTwoTerm T G L n) - atkinsonLeadingSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonCorrectionSum_le
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth hs
  rw [tsum_zetaAtkinsonTwoTerm_eq_leading_sub_correction_of_summable
    hT hG hGT hL hwidth hs, sub_sub_cancel_left, norm_neg]
  exact hbound T G L hT hG hGT hL hwidth

end MathCollab.Density.Stronger.Atkinson
