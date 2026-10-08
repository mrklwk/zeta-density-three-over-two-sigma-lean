module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices and native assembly using revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. See third_party/twelfth/ATKINSON_LOCAL_SOURCE_MANIFEST.json.
Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonTwoTermSource
public import MathCollab.Density.Stronger.Atkinson.AtkinsonTwoTermStationary
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationarySourceAssembly

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

noncomputable section
open Complex Filter MeasureTheory
namespace MathCollab.Density.Stronger.Atkinson

/-- The actual local second moment is controlled by the actual complete
stationary sum, with one constant and threshold before both physical variables.
All source, Bessel, correction, tail and stationary estimates are native proofs. -/
theorem exists_zetaSquareLocalMean_le_atkinson_stationary {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → T ^ (1 / 4 + κ) ≤ G →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (atkinsonStationaryLeadingSum T G (Real.log T)).re +
          C * G * Real.log T := by
  obtain ⟨C, hC, B, _, hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_twoTerm hδ
  obtain ⟨D, hD, E, _, hstationary⟩ :=
    exists_tsum_zetaAtkinsonTwoTerm_sub_stationary_above_fourthRoot hδ hκ
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ,
      T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → T ^ (1 / 4 + κ) ≤ G →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (atkinsonStationaryLeadingSum T G (Real.log T)).re +
          (C + 2 * Real.exp 1 * D) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ,
      eventually_ge_atTop B, eventually_ge_atTop E] with T hscale hTB hTE
    intro G hlower hupper hquarter
    have hT0 : 0 < T := by linarith [hscale.1]
    have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
    have hm := hsource T G hTB hlower hupper
    have he := hstationary T G hTE hlower hupper hquarter
    change ‖zetaAtkinsonTwoTermSum T G (Real.log T) -
      atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ D * G at he
    have hr := (Complex.re_le_norm
      (zetaAtkinsonTwoTermSum T G (Real.log T) -
        atkinsonStationaryLeadingSum T G (Real.log T))).trans he
    simp only [Complex.sub_re] at hr
    have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * Real.exp 1)
    have hGlog : G ≤ G * Real.log T := by nlinarith [hscale.2.1]
    have herror := mul_le_mul_of_nonneg_left hGlog
      (by positivity : 0 ≤ 2 * Real.exp 1 * D)
    nlinarith
  obtain ⟨U, hU⟩ := eventually_atTop.mp hev
  refine ⟨C + 2 * Real.exp 1 * D, by positivity,
    max 40000 U, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper hquarter
  exact hU T ((le_max_right _ _).trans hT) G hlower hupper hquarter

/-- The final local-mean producer has no analytic premise. -/
theorem localMeanStationaryInput_native : LocalMeanStationaryInput := by
  intro δ κ hδ hκ
  exact exists_zetaSquareLocalMean_le_atkinson_stationary hδ hκ

end MathCollab.Density.Stronger.Atkinson
