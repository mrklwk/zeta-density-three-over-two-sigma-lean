module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices and native assembly using revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. See third_party/twelfth/ATKINSON_LOCAL_SOURCE_MANIFEST.json.
Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonMinusSource
public import MathCollab.Density.Stronger.Atkinson.ZetaNeumannSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Actual zeta source with the two-term Neumann expansion

The full arithmetic replacement is consumed by the physical Gaussian
and local-mean theorems. All errors share one uniform logarithmic bound.
Stationary-phase evaluation of this oscillatory series remains separate.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Filter MeasureTheory

namespace MathCollab.Density.Stronger.Atkinson

theorem exists_zetaAtkinsonBesselMinus_twoTerm_log_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselMinus T G (Real.log T) -
        zetaAtkinsonTwoTermSum T G (Real.log T)‖ ≤ C * G * Real.log T := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselMinus T G (Real.log T) -
        zetaAtkinsonTwoTermSum T G (Real.log T)‖ ≤ C * G * Real.log T := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ] with T hsupport hscale
    intro G hlower hupper
    obtain ⟨hG, hlog, hwidth, _⟩ := hsupport.2 G hlower
    apply (hbound T G (Real.log T) hsupport.1 hG
      (hscale.2.2 G hG hupper).1 hlog hwidth).trans
    exact le_mul_of_one_le_right (mul_nonneg hC.le hG.le) hscale.2.1
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨C, hC, max 16 B, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper

theorem exists_zetaSquarePhysicalGaussian_atkinson_twoTerm_approximation
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaAtkinsonTwoTermSum T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ :=
    exists_zetaSquarePhysicalGaussian_atkinson_minus_approximation hδ
  obtain ⟨D, hD, B₁, _, herror⟩ := exists_zetaAtkinsonBesselMinus_twoTerm_log_bound hδ
  refine ⟨C + 2 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper
  have hr := (Complex.abs_re_le_norm
    (zetaAtkinsonBesselMinus T G (Real.log T) -
      zetaAtkinsonTwoTermSum T G (Real.log T))).trans he
  simp only [Complex.sub_re] at hr
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hm).1, (abs_le.mp hm).2,
    (abs_le.mp hr).1, (abs_le.mp hr).2]

theorem exists_zetaSquareLocalMean_le_atkinson_twoTerm {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonTwoTermSum T G (Real.log T)).re +
          C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_minus hδ
  obtain ⟨D, hD, B₁, _, herror⟩ := exists_zetaAtkinsonBesselMinus_twoTerm_log_bound hδ
  refine ⟨C + 2 * Real.exp 1 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper
  have hr := (Complex.re_le_norm
    (zetaAtkinsonBesselMinus T G (Real.log T) -
      zetaAtkinsonTwoTermSum T G (Real.log T))).trans he
  simp only [Complex.sub_re] at hr
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * Real.exp 1)
  nlinarith

end MathCollab.Density.Stronger.Atkinson
