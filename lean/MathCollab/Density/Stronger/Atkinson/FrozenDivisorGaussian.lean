module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightFreezing
public import MathCollab.Density.Stronger.Atkinson.GammaGaussianTransform

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaFrozenDivisorCoefficient (T : ℝ) (n : ℕ) : ℂ :=
  divisorDirichletTerm (afeCriticalPoint (-T)) n *
    zetaDivisorWeight (zetaDivisorWeightArgument T n)

def zetaFrozenDivisorGaussianMean (T G : ℝ) : ℂ :=
  ∫ x : ℝ, zetaSquareFrozenDivisorIntegral T x * (Real.exp (-(x / G) ^ 2) : ℂ)

def zetaFrozenDivisorQuadraticSum (T G : ℝ) : ℂ :=
  ∑' n : ℕ, zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
    zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))

theorem divisorDirichletTerm_height_shift (T x : ℝ) (n : ℕ) :
    divisorDirichletTerm (afeCriticalPoint (-(T + x))) n =
      divisorDirichletTerm (afeCriticalPoint (-T)) n *
        Complex.exp (I * (Real.log (n : ℝ) : ℂ) * x) := by
  have hs : afeCriticalPoint (-(T + x)) = afeCriticalPoint (-T) + -(x : ℂ) * I := by
    unfold afeCriticalPoint
    push_cast
    ring
  rw [hs, divisorDirichletTerm_add_eq_mul_exp]
  congr 2
  ring

theorem zetaSquareFrozenDivisorContribution_eq_phase (T x : ℝ) (n : ℕ) :
    zetaSquareFrozenDivisorContribution T x n = zetaFrozenDivisorCoefficient T n *
      zetaSquareReflectedGammaPhase (T + x) * Complex.exp (I * (Real.log (n : ℝ) : ℂ) * x) := by
  unfold zetaSquareFrozenDivisorContribution zetaFrozenDivisorCoefficient
  rw [divisorDirichletTerm_height_shift]
  ring

theorem zetaSquareFrozenDivisorContribution_mul_gaussian (T G x : ℝ) (n : ℕ) :
    zetaSquareFrozenDivisorContribution T x n * (Real.exp (-(x / G) ^ 2) : ℂ) =
      zetaFrozenDivisorCoefficient T n * zetaSquareGammaGaussianIntegrand T G (Real.log (n : ℝ)) x := by
  rw [zetaSquareFrozenDivisorContribution_eq_phase]
  unfold zetaSquareGammaGaussianIntegrand
  ring

theorem summable_norm_zetaFrozenDivisorCoefficient {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℕ => ‖zetaFrozenDivisorCoefficient T n‖) := by
  simpa only [zetaFrozenDivisorCoefficient, norm_mul] using
    summable_norm_source_divisor_weight hT (-T)

theorem integrable_zetaFrozenDivisorGaussianTerm (T : ℝ) {G : ℝ}
    (hG : G ≠ 0) (n : ℕ) :
    Integrable (fun x : ℝ => zetaSquareFrozenDivisorContribution T x n *
      (Real.exp (-(x / G) ^ 2) : ℂ)) := by
  simp_rw [zetaSquareFrozenDivisorContribution_mul_gaussian]
  exact (integrable_zetaSquareGammaGaussianIntegrand T (Real.log (n : ℝ)) hG).const_mul _

theorem summable_integral_norm_zetaFrozenDivisorGaussianTerm {T : ℝ} (hT : 0 < T) (G : ℝ) :
    Summable (fun n : ℕ => ∫ x : ℝ, ‖zetaSquareFrozenDivisorContribution T x n *
      (Real.exp (-(x / G) ^ 2) : ℂ)‖) := by
  simp_rw [zetaSquareFrozenDivisorContribution_mul_gaussian, norm_mul,
    norm_zetaSquareGammaGaussianIntegrand, integral_const_mul]
  exact (summable_norm_zetaFrozenDivisorCoefficient hT).mul_right _

/-- Actual Gaussian averaging of the complete frozen source, not a
formal exchange or a independently supplied transformed series. -/
theorem hasSum_zetaFrozenDivisorGaussianMean {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0) :
    HasSum (fun n : ℕ => zetaFrozenDivisorCoefficient T n *
      zetaSquareGammaGaussianTransform T G (Real.log (n : ℝ)))
      (zetaFrozenDivisorGaussianMean T G) := by
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_zetaFrozenDivisorGaussianTerm T hG)
    (summable_integral_norm_zetaFrozenDivisorGaussianTerm hT G)
  simp_rw [tsum_mul_right] at h
  change HasSum _ (zetaFrozenDivisorGaussianMean T G) at h
  simp_rw [zetaSquareFrozenDivisorContribution_mul_gaussian, integral_const_mul] at h
  exact h

theorem norm_zetaGaussianQuadraticIntegral_le_mass {T G : ℝ} (hT : 0 < T)
    (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖zetaGaussianQuadraticIntegral T G v‖ ≤ Real.sqrt Real.pi * G := by
  apply (norm_zetaGaussianQuadraticIntegral_le hT hG hGT v).trans
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (G * v)]))

theorem summable_zetaFrozenDivisorQuadraticTerm {T G : ℝ} (hT : 0 < T)
    (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) :
    Summable (fun n : ℕ => zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))) := by
  apply summable_norm_iff.mp
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (f := fun n : ℕ => ‖zetaFrozenDivisorCoefficient T n‖ * (Real.sqrt Real.pi * G))
  · intro n
    simp only [norm_mul, norm_zetaSquareReflectedGammaPhase, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_zetaGaussianQuadraticIntegral_le_mass hT hG hGT _)
      (norm_nonneg _)
  · exact (summable_norm_zetaFrozenDivisorCoefficient hT).mul_right _

/-- Uniform phase-replacement error for the actual, absolutely convergent
divisor transform. No arithmetic cancellation is claimed by this bound. -/
theorem norm_zetaFrozenDivisorGaussianMean_sub_quadratic_le {T G r : ℝ}
    (hT : 4 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hr : 0 ≤ r) (hrT : r ≤ T / 2) :
    ‖zetaFrozenDivisorGaussianMean T G - zetaFrozenDivisorQuadraticSum T G‖ ≤
      (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
        (2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
          2 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2)) := by
  let E : ℝ := 2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
    2 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2)
  let e := fun n : ℕ => zetaFrozenDivisorCoefficient T n *
    (zetaSquareGammaGaussianTransform T G (Real.log (n : ℝ)) -
      zetaSquareReflectedGammaPhase T * zetaGaussianQuadraticIntegral T G
        (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))))
  have hT0 : 0 < T := by linarith
  have hpoint (n : ℕ) : ‖e n‖ ≤ ‖zetaFrozenDivisorCoefficient T n‖ * E := by
    dsimp only [e]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_zetaSquareGammaGaussianTransform_sub_quadratic_le hT hG hr hrT _) (norm_nonneg _)
  have hsum : HasSum e (zetaFrozenDivisorGaussianMean T G - zetaFrozenDivisorQuadraticSum T G) := by
    convert (hasSum_zetaFrozenDivisorGaussianMean hT0 hG.ne').sub
      (summable_zetaFrozenDivisorQuadraticTerm hT0 hG hGT).hasSum using 1
    · funext n
      dsimp only [e, Pi.sub_apply]
      ring
    · rfl
  have hnorm : Summable (fun n => ‖e n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpoint
      ((summable_norm_zetaFrozenDivisorCoefficient hT0).mul_right E)
  rw [← hsum.tsum_eq]
  calc
    _ ≤ ∑' n : ℕ, ‖e n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖ * E :=
      Summable.tsum_le_tsum hpoint hnorm ((summable_norm_zetaFrozenDivisorCoefficient hT0).mul_right E)
    _ = _ := tsum_mul_right

/-- Square-root-scale source consumer, with one constant for all allowed
heights, Gaussian widths and phase-replacement windows. -/
theorem exists_norm_zetaFrozenDivisorGaussianMean_sub_quadratic_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G r : ℝ, 4 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 ≤ r → r ≤ T / 2 →
      ‖zetaFrozenDivisorGaussianMean T G - zetaFrozenDivisorQuadraticSum T G‖ ≤
        C * T ^ (1 / 2 + ε) *
          (2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
            2 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_tsum_norm_source_divisor_weight_le ε hε
  refine ⟨C, hC, ?_⟩
  intro T G r hT hG hGT hr hrT
  apply (norm_zetaFrozenDivisorGaussianMean_sub_quadratic_le hT hG hGT hr hrT).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [zetaFrozenDivisorCoefficient, norm_mul] using hbound T (by linarith) (-T)

end MathCollab.Density.Stronger.Atkinson
