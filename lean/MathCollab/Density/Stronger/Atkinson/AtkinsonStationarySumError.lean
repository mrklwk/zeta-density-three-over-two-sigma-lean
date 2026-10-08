module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSourceBand
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFiniteSourceError

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex Filter
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_atkinsonLeadingSum_sub_stationary_bound {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingSum T G (Real.log T)-atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*(G+T^(1/4+ε)) := by
  obtain ⟨A,hA,B,hB,hfinite⟩ := exists_atkinsonStationary_finite_power_error hδ hε
  obtain ⟨D,hD,E,_,htail⟩ := exists_atkinsonLeading_source_band_bound hδ
  refine ⟨A+D,by positivity,max B E,hB.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hT0 : 0 < T := by linarith [hB.trans ((le_max_left B E).trans hT)]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hf := hfinite T G ((le_max_left _ _).trans hT) hlower hupper hquarter
  have ht := htail T G ((le_max_right _ _).trans hT) hlower hupper
    (atkinsonSourceCutoff T G (Real.log T)) (atkinsonSourceCutoff_lower _ _ _)
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add ht hf).trans ?_)
  nlinarith [Real.rpow_pos_of_pos hT0 (1/4+ε)]

theorem exists_atkinsonLeadingSum_sub_stationary_above_fourthRoot {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      ‖atkinsonLeadingSum T G (Real.log T)-atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G := by
  obtain ⟨C,hC,B,hB,hbound⟩ := exists_atkinsonLeadingSum_sub_stationary_bound hδ hκ
  refine ⟨2*C,by positivity,B,hB,?_⟩
  intro T G hT hlower hupper hquarter
  have hT1 : 1 ≤ T := by linarith
  have hq : T^(1/4 : ℝ) ≤ G :=
    (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : (1/4:ℝ) ≤ 1/4+κ)).trans hquarter
  apply (hbound T G hT hlower hupper hq).trans
  nlinarith

end MathCollab.Density.Stronger.Atkinson
