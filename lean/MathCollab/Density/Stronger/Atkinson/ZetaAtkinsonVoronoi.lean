module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected ZetaAtkinsonVoronoi.lean proofs,
revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Uses the new native modulus-one contour/absolute-exchange proof and physically
proved Y0/K0 Mellin bridges. Mathlib attribution remains Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.OrdinaryDivisorVoronoi
public import MathCollab.Density.Stronger.Atkinson.VoronoiMinusTransport
public import MathCollab.Density.Stronger.Atkinson.BesselTransformBridge
public import MathCollab.Density.Stronger.Atkinson.AtkinsonVoronoiTerms
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSource

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem ordinaryDivisorVoronoi_bessel {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n * g n) =
      (∫ x : ℝ in Ioi 0, ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * g x) +
        (∑' n : ℕ, divisorWeight n * (-(2 * Real.pi) : ℂ) *
          ∫ x : ℝ in Ioi 0, g x * (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)) +
        ∑' n : ℕ, divisorWeight n * 4 *
          ∫ x : ℝ in Ioi 0, g x * (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ) := by
  have hminus (n : ℕ) : divisorWeight n * dfiVoronoiMinusTransform 1 (mellin g) n =
      divisorWeight n * (-(2 * Real.pi) : ℂ) *
        ∫ x : ℝ in Ioi 0, g x * (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ) := by
    by_cases hn : n = 0
    · simp [hn, divisorWeight]
    · have h := dfiVoronoiMinusTransform_mellin_eq_bessel 1 n (Nat.pos_of_ne_zero hn) hg
      change dfiVoronoiMinusTransform 1 (mellin g) n = _ at h
      rw [h]
      simp only [dfiVoronoiMinusBesselTransform, Nat.cast_one, div_one, mul_assoc]
  have hplus (n : ℕ) : divisorWeight n * dfiVoronoiPlusTransform 1 (mellin g) n =
      divisorWeight n * 4 *
        ∫ x : ℝ in Ioi 0, g x * (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ) := by
    by_cases hn : n = 0
    · simp [hn, divisorWeight]
    · rw [dfiVoronoiPlusTransform_mellin_eq_bessel 1 n (Nat.pos_of_ne_zero hn) hg]
      simp only [dfiVoronoiPlusBesselTransform, Nat.cast_one, div_one, mul_assoc]
  rw [ordinaryDivisorVoronoi_native hg]
  simp_rw [hminus, hplus]
  rfl
theorem zetaSmoothDivisorSum_eq_atkinson_bessel {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    zetaSmoothDivisorSum T G L = zetaAtkinsonVoronoiMain T G L +
      zetaAtkinsonBesselMinus T G L + zetaAtkinsonBesselPlus T G L := by
  rw [zetaSmoothDivisorSum_eq_atkinson_test]
  exact ordinaryDivisorVoronoi_bessel (zetaAtkinsonDivisorVoronoiTest hT hG hL)

theorem exists_zetaSquarePhysicalGaussian_atkinson_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T) +
          zetaAtkinsonBesselPlus T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareGaussianMean_smooth_approximation hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hupper
  have hT8 := hT₀.trans hT
  rw [← zetaSquareGaussianMean_eq_physical T hG,
    ← zetaSmoothDivisorSum_eq_atkinson_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hupper

theorem exists_zetaSquareLocalMean_le_atkinson_bessel {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T) + zetaAtkinsonBesselPlus T G (Real.log T)).re +
            C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareLocalMean_le_smooth_divisor hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hupper
  have hT8 := hT₀.trans hT
  rw [← zetaSmoothDivisorSum_eq_atkinson_bessel (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hupper

end MathCollab.Density.Stronger.Atkinson
