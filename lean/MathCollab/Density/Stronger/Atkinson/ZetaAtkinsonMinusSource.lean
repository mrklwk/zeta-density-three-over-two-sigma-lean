module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices and native assembly using revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. See third_party/twelfth/ATKINSON_LOCAL_SOURCE_MANIFEST.json.
Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonReducedSource
public import MathCollab.Density.Stronger.Atkinson.AtkinsonMainIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# The actual physical source with only its oscillatory Y0 sum remaining

Both removed branches are paid for by proved bounds on their actual
complete integrals. The resulting source keeps the full divisor sum,
its normalization and one uniform logarithmic error constant.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex MeasureTheory

namespace MathCollab.Density.Stronger.Atkinson

theorem exists_zetaSquarePhysicalGaussian_atkinson_minus_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaAtkinsonBesselMinus T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquarePhysicalGaussian_atkinson_reduced hδ
  obtain ⟨D, hD, B₁, hB₁, hmain⟩ := exists_zetaAtkinsonVoronoiMain_log_bound hδ
  refine ⟨C + 2 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have hk := hmain T G ((le_max_right _ _).trans hT) hlower hupper
  have hkr := (Complex.abs_re_le_norm (zetaAtkinsonVoronoiMain T G (Real.log T))).trans hk
  simp only [Complex.add_re] at hm
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hm).1, (abs_le.mp hm).2,
    (abs_le.mp hkr).1, (abs_le.mp hkr).2]

theorem exists_zetaSquareLocalMean_le_atkinson_minus {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonBesselMinus T G (Real.log T)).re +
          C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_reduced hδ
  obtain ⟨D, hD, B₁, hB₁, hmain⟩ := exists_zetaAtkinsonVoronoiMain_log_bound hδ
  refine ⟨C + 2 * Real.exp 1 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have hk := hmain T G ((le_max_right _ _).trans hT) hlower hupper
  have hkr := (Complex.re_le_norm (zetaAtkinsonVoronoiMain T G (Real.log T))).trans hk
  have hscaled := mul_le_mul_of_nonneg_left hkr (by positivity : 0 ≤ 2 * Real.exp 1)
  simp only [Complex.add_re] at hm
  nlinarith

end MathCollab.Density.Stronger.Atkinson
