module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Series algebra adapted from AtkinsonLeadingSeries at exact source revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, with native band convergence.
See third_party/twelfth/ATKINSON_LEADING_CONVERGENCE_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLeadingSeriesAlgebra
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSharpTruncation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson

/-- Genuine convergence follows from the actual band bound, independently of the
physical Voronoi source identity. -/
theorem summable_zetaAtkinsonTwoTerm_of_band {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 1 ≤ G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 1 ≤ L) (hwidth : 8 * L ≤ G) :
    Summable (zetaAtkinsonTwoTerm T G L) :=
  (summable_atkinsonLeadingTerm_iff_twoTerm hT (by linarith) hGT
    (by linarith) hwidth).mp
    (summable_atkinsonLeadingTerm_of_band hT hG hGT hL hwidth)

theorem tsum_zetaAtkinsonTwoTerm_eq_leading_sub_correction {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 1 ≤ G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 1 ≤ L) (hwidth : 8 * L ≤ G) :
    (∑' n : ℕ, zetaAtkinsonTwoTerm T G L n) =
      atkinsonLeadingSum T G L - atkinsonCorrectionSum T G L :=
  tsum_zetaAtkinsonTwoTerm_eq_leading_sub_correction_of_summable
    hT (by linarith) hGT (by linarith) hwidth
    (summable_atkinsonLeadingTerm_of_band hT hG hGT hL hwidth)

theorem exists_norm_tsum_zetaAtkinsonTwoTerm_sub_leading_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
        ‖(∑' n : ℕ, zetaAtkinsonTwoTerm T G L n) - atkinsonLeadingSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_tsum_zetaAtkinsonTwoTerm_sub_leading_le_of_summable
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  exact hbound T G L hT (by linarith) hGT (by linarith) hwidth
    (summable_atkinsonLeadingTerm_of_band hT hG hGT hL hwidth)

end MathCollab.Density.Stronger.Atkinson
