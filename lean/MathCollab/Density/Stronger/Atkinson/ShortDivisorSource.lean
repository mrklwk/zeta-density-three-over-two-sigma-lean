module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.SourceErrorScales

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


/-- One height threshold precedes every permitted positive Gaussian
width. The conclusion concerns the actual whole-line zeta mean. -/
theorem exists_zetaSquareGaussianMean_short_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |zetaSquareGaussianMean T G - 2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re| ≤
        C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hwindow⟩ := exists_zetaSquareGaussianWindow_log_error hδ
  obtain ⟨B₁, hB₁, hzeta⟩ := exists_zetaSquareGaussian_log_tail_bound 0
  obtain ⟨B₂, hB₂, hdivisor⟩ := exists_zetaQuadraticDivisor_log_tail_bound 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |zetaSquareGaussianMean T G - 2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re| ≤
        (C + 3) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop B,
      eventually_ge_atTop B₁, eventually_ge_atTop B₂] with T hscale hTB hTB₁ hTB₂
    intro G hG hwidth
    obtain ⟨hGT, _, hGT'⟩ := hscale.2.2 G hG hwidth
    have hmain := hwindow T G hTB hG hwidth
    obtain ⟨hz0, hz⟩ := hzeta T G hTB₁ hG hGT'
    have hd := hdivisor T G hTB₂ hG hGT
    simp only [neg_zero, Real.rpow_zero, mul_one] at hz hd
    have hzabs : |zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G (Real.log T)| ≤ G := by
      rw [abs_of_nonneg hz0]
      exact hz
    have hre : |2 * (zetaFrozenDivisorQuadraticSum T G).re -
        2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re| ≤ 2 * G := by
      rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply le_trans ?_ hd
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm
        (zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G (Real.log T))
    have htri₁ := abs_sub_le (zetaSquareGaussianMean T G)
      (zetaSquareGaussianWindow T G (Real.log T)) (2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re)
    have htri₂ := abs_sub_le (zetaSquareGaussianWindow T G (Real.log T))
      (2 * (zetaFrozenDivisorQuadraticSum T G).re) (2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re)
    have hGlog : G ≤ G * Real.log T := by nlinarith [hscale.2.1]
    nlinarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨C + 3, by positivity, max 8 T₁, le_max_left _ _, ?_⟩
  intro T G hT hG hwidth
  exact hT₁ T ((le_max_right _ _).trans hT) G hG hwidth

theorem exists_zetaSquarePhysicalGaussian_short_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareGaussianMean_short_approximation hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hwidth
  rw [← zetaSquareGaussianMean_eq_physical T hG]
  exact hbound T G hT hG hwidth

/-- The actual unsmoothed local second moment enters the finite,
oscillatory divisor source. The finite source itself still requires
the genuine Voronoi/stationary-phase analysis. -/
theorem exists_zetaSquareLocalMean_le_short_divisor {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re + C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareGaussianMean_short_approximation hδ
  obtain ⟨B₁, hB₁, hzeta⟩ := exists_zetaSquareGaussian_log_tail_bound 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re +
          (Real.exp 1 * C) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop B,
      eventually_ge_atTop B₁] with T hscale hTB hTB₁
    intro G hG hwidth
    have hlocal := zetaSquareLocalMean_le_gaussian_window (T := T) hG hscale.2.1
    have hz0 := (hzeta T G hTB₁ hG (hscale.2.2 G hG hwidth).2.2).1
    have herror := (le_abs_self _).trans (hsource T G hTB hG hwidth)
    calc
      _ ≤ Real.exp 1 * zetaSquareGaussianWindow T G (Real.log T) := hlocal
      _ ≤ Real.exp 1 * zetaSquareGaussianMean T G :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re + C * G * Real.log T) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = _ := by ring
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨Real.exp 1 * C, by positivity, max 8 T₁, le_max_left _ _, ?_⟩
  intro T G hT hG hwidth
  exact hT₁ T ((le_max_right _ _).trans hT) G hG hwidth

end MathCollab.Density.Stronger.Atkinson
