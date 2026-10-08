module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Source-scale algebra adapted from AtkinsonLeadingSource at exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1; native convergence and stationary joins.
See third_party/twelfth/ATKINSON_LEADING_CONVERGENCE_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLeadingSeriesConvergence
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationarySumError
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport
public import MathCollab.Density.Stronger.Atkinson.SourceLogScales

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

noncomputable section
open Complex Filter
namespace MathCollab.Density.Stronger.Atkinson

/-- Complete two-term source to complete leading source, with all physical scales
uniform and convergence already supplied by the native band estimate. -/
theorem exists_tsum_zetaAtkinsonTwoTerm_sub_leading_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖(∑' n : ℕ, zetaAtkinsonTwoTerm T G (Real.log T) n) -
        atkinsonLeadingSum T G (Real.log T)‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_tsum_zetaAtkinsonTwoTerm_sub_leading_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖(∑' n : ℕ, zetaAtkinsonTwoTerm T G (Real.log T) n) -
        atkinsonLeadingSum T G (Real.log T)‖ ≤ C * G := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ] with T hsupport hscale
    intro G hlower hupper
    obtain ⟨hG, _, hwidth, _⟩ := hsupport.2 G hlower
    have hT1 : 1 ≤ T := by linarith [hsupport.1]
    have hG1 : 1 ≤ G := (Real.one_le_rpow hT1 hδ.le).trans hlower
    exact hbound T G (Real.log T) hT1 hG1
      (hscale.2.2 G hG hupper).1 hscale.2.1 hwidth
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨C, hC, max 16 B, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper

/-- The full original two-term arithmetic series is within O(G) of the exact
stationary series above fourth-root width. This asserts no zeta-source identity. -/
theorem exists_tsum_zetaAtkinsonTwoTerm_sub_stationary_above_fourthRoot
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → T ^ (1 / 4 + κ) ≤ G →
      ‖(∑' n : ℕ, zetaAtkinsonTwoTerm T G (Real.log T) n) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ C * G := by
  obtain ⟨C, hC, B, _, hcorrection⟩ := exists_tsum_zetaAtkinsonTwoTerm_sub_leading_bound hδ
  obtain ⟨D, hD, E, hE, hstationary⟩ :=
    exists_atkinsonLeadingSum_sub_stationary_above_fourthRoot hδ hκ
  refine ⟨C + D, by positivity, max B E, hE.trans (le_max_right _ _), ?_⟩
  intro T G hT hlower hupper hquarter
  have hc := hcorrection T G ((le_max_left _ _).trans hT) hlower hupper
  have hs := hstationary T G ((le_max_right _ _).trans hT) hlower hupper hquarter
  apply (norm_sub_le_norm_sub_add_norm_sub _ (atkinsonLeadingSum T G (Real.log T)) _).trans
  calc
    _ ≤ C * G + D * G := add_le_add hc hs
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
