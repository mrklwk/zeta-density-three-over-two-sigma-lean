module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.QuadraticDivisorBand
public import MathCollab.Density.Stronger.Atkinson.FrozenWindow

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


theorem norm_zetaFrozenDivisorQuadraticSum_sub_short_le {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 ≤ L) :
    ‖zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G L‖ ≤
      (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
        (Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) := by
  classical
  let S := zetaQuadraticDivisorBand T G L
  let f := fun n : ℕ => zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
    zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))
  let B := Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)
  have hf : Summable f := summable_zetaFrozenDivisorQuadraticTerm hT hG hGT
  have hc := summable_norm_zetaFrozenDivisorCoefficient hT
  have hpoint (n : {n : ℕ // n ∉ S}) : ‖f n‖ ≤ ‖zetaFrozenDivisorCoefficient T n‖ * B :=
    norm_zetaQuadraticDivisorTerm_off_band_le hT hG hGT hL n.2
  change ‖(∑' n, f n) - ∑ n ∈ S, f n‖ ≤ _
  rw [← hf.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
  calc
    _ ≤ ∑' n : {n : ℕ // n ∉ S}, ‖f n‖ := norm_tsum_le_tsum_norm (hf.norm.subtype _)
    _ ≤ ∑' n : {n : ℕ // n ∉ S}, ‖zetaFrozenDivisorCoefficient T n‖ * B :=
      (hf.norm.subtype _).tsum_le_tsum hpoint ((hc.subtype _).mul_right B)
    _ = (∑' n : {n : ℕ // n ∉ S}, ‖zetaFrozenDivisorCoefficient T n‖) * B := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Summable.tsum_subtype_le (fun n : ℕ => ‖zetaFrozenDivisorCoefficient T n‖)
        (fun n => n ∉ S) (fun _ => norm_nonneg _) hc) (by dsimp [B]; positivity)

/-- The omitted source has a uniform square-root coefficient factor,
not a height-dependent constant chosen after the Gaussian width. -/
theorem exists_norm_zetaFrozenDivisorQuadraticSum_sub_short_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T → 0 ≤ L →
      ‖zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G L‖ ≤
        C * T ^ (1 / 2 + ε) * G * Real.exp (-L ^ 2 / 8) := by
  obtain ⟨C, hC, hmass⟩ := exists_tsum_norm_source_divisor_weight_le ε hε
  refine ⟨C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hG hGT hL
  apply (norm_zetaFrozenDivisorQuadraticSum_sub_short_le (by linarith) hG hGT hL).trans
  have hm : (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) ≤ C * T ^ (1 / 2 + ε) := by
    simpa only [zetaFrozenDivisorCoefficient, norm_mul] using hmass T hT (-T)
  calc
    _ ≤ (C * T ^ (1 / 2 + ε)) * (Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by ring

/-- The finite shortened series consumes the actual Gaussian zeta window.
Physical-window radius and frequency-cutoff radius remain independent;
both explicit tail losses are present. -/
theorem exists_abs_zetaSquareGaussianWindow_sub_short_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G r L : ℝ, 8 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 ≤ r → r ≤ T / 2 → 0 ≤ L →
      |zetaSquareGaussianWindow T G (r / G) - 2 * (zetaShortQuadraticDivisorSum T G L).re| ≤
        C * r * (1 + r * T ^ (-1 / 2 + ε)) +
          (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
            (4 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
              6 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) +
              2 * Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_zetaSquareGaussianWindow_sub_quadratic_le ε hε
  refine ⟨C, hC, ?_⟩
  intro T G r L hT hG hGT hr hrT hL
  have hmain := hbound T G r hT hG hGT hr hrT
  have htail := norm_zetaFrozenDivisorQuadraticSum_sub_short_le (by linarith : 0 < T) hG hGT hL
  have hre : |2 * (zetaFrozenDivisorQuadraticSum T G).re - 2 * (zetaShortQuadraticDivisorSum T G L).re| ≤
      2 * ‖zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G L‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm
      (zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G L)
  have htri := abs_sub_le (zetaSquareGaussianWindow T G (r / G))
    (2 * (zetaFrozenDivisorQuadraticSum T G).re) (2 * (zetaShortQuadraticDivisorSum T G L).re)
  nlinarith

end MathCollab.Density.Stronger.Atkinson
