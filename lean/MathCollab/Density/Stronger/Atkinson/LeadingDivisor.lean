module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.KernelApproximation

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


def zetaSquareLeadingDivisorTerm (t : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  divisorDirichletTerm (afeCriticalPoint (-t) + (1 + (u : ℂ) * I)) n *
    zetaSquareLeadingRightKernel t u

def zetaSquareLeadingDivisorContribution (t : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, zetaSquareLeadingDivisorTerm t n u

def zetaSquareLeadingDivisorIntegral (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
    LSeries (fun n : ℕ => (n.divisors.card : ℂ)) (afeCriticalPoint (-t) + (1 + (u : ℂ) * I)) *
      zetaSquareLeadingRightKernel t u

theorem norm_zetaSquareLeadingDivisorTerm (t : ℝ) (n : ℕ) (u : ℝ) :
    ‖zetaSquareLeadingDivisorTerm t n u‖ =
      ‖divisorDirichletTerm (3 / 2) n‖ * ‖zetaSquareLeadingRightKernel t u‖ := by
  simp only [zetaSquareLeadingDivisorTerm, norm_mul, divisorDirichletTerm, LSeries.norm_term_eq]
  norm_num [afeCriticalPoint]

theorem integrable_zetaSquareLeadingDivisorTerm {t : ℝ} (ht : 4 ≤ t) (n : ℕ) :
    Integrable (zetaSquareLeadingDivisorTerm t n) := by
  unfold zetaSquareLeadingDivisorTerm
  apply (integrable_zetaSquareLeadingRightKernel ht).bdd_mul
    (c := ‖divisorDirichletTerm (3 / 2) n‖)
  · simpa using (continuous_divisorDirichletTerm_vertical (-t) 1 n).aestronglyMeasurable
  · filter_upwards with u
    simp only [divisorDirichletTerm, LSeries.norm_term_eq]
    norm_num [afeCriticalPoint]

theorem summable_integral_norm_zetaSquareLeadingDivisorTerm (t : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖zetaSquareLeadingDivisorTerm t n u‖) := by
  simp_rw [norm_zetaSquareLeadingDivisorTerm, integral_const_mul]
  exact (summable_divisorDirichletTerm (s := (3 / 2 : ℂ)) (by norm_num)).norm.mul_right _

theorem hasSum_zetaSquareLeadingDivisorContribution {t : ℝ} (ht : 4 ≤ t) :
    HasSum (zetaSquareLeadingDivisorContribution t) (zetaSquareLeadingDivisorIntegral t) := by
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_zetaSquareLeadingDivisorTerm ht) (summable_integral_norm_zetaSquareLeadingDivisorTerm t)
  simp only [zetaSquareLeadingDivisorTerm, tsum_mul_right, tsum_divisorDirichletTerm] at h
  exact h.mul_left (1 / (2 * Real.pi) : ℂ)

theorem norm_zetaSquareDivisorTerm_error (t : ℝ) (n : ℕ) (u : ℝ) :
    ‖zetaSquareDivisorTerm (-t) n u / zetaSquareGammaNormalization t -
      zetaSquareLeadingDivisorTerm t n u‖ =
      ‖divisorDirichletTerm (3 / 2) n‖ *
        ‖zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t -
          zetaSquareLeadingRightKernel t u‖ := by
  unfold zetaSquareDivisorTerm zetaSquareLeadingDivisorTerm
  rw [mul_div_assoc, ← mul_sub, norm_mul]
  simp only [divisorDirichletTerm, LSeries.norm_term_eq]
  norm_num [afeCriticalPoint]

/-- One constant controls every actual coefficientwise error, with the
ordinary absolutely summable divisor weight retained explicitly. -/
theorem exists_norm_zetaSquareDivisorContribution_error_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ t → ∀ n : ℕ,
      ‖zetaSquareDivisorContribution (-t) n / zetaSquareGammaNormalization t -
        zetaSquareLeadingDivisorContribution t n‖ ≤ C * ‖divisorDirichletTerm (3 / 2) n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_zetaSquareRightKernel_error_le
  have hnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  refine ⟨C / (2 * Real.pi), by positivity, ?_⟩
  intro t ht n
  have ha := (integrable_zetaSquareDivisorTerm (-t) n).div_const (zetaSquareGammaNormalization t)
  have hb := integrable_zetaSquareLeadingDivisorTerm ht n
  have heq : zetaSquareDivisorContribution (-t) n / zetaSquareGammaNormalization t -
      zetaSquareLeadingDivisorContribution t n =
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        zetaSquareDivisorTerm (-t) n u / zetaSquareGammaNormalization t -
          zetaSquareLeadingDivisorTerm t n u := by
    rw [integral_sub ha hb, integral_div]
    unfold zetaSquareDivisorContribution zetaSquareLeadingDivisorContribution
    ring
  rw [heq, norm_mul, hnorm]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∫ u : ℝ,
        ‖zetaSquareDivisorTerm (-t) n u / zetaSquareGammaNormalization t -
          zetaSquareLeadingDivisorTerm t n u‖ := by
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = (1 / (2 * Real.pi)) * (‖divisorDirichletTerm (3 / 2) n‖ * ∫ u : ℝ,
        ‖zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t -
          zetaSquareLeadingRightKernel t u‖) := by
      simp_rw [norm_zetaSquareDivisorTerm_error, integral_const_mul]
    _ ≤ (1 / (2 * Real.pi)) * (‖divisorDirichletTerm (3 / 2) n‖ * C) := by
      gcongr
      exact hbound t ht
    _ = _ := by ring

/-- Uniform complete-series source approximation. Neither convergence nor
the remainder is an input, and the actual source Gamma normalization is
retained. This does not claim a shortened sum or a twelfth-moment theorem. -/
theorem exists_norm_zetaSquareDivisorIntegral_sub_leading_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ t →
      ‖zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t -
        zetaSquareLeadingDivisorIntegral t‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSquareDivisorContribution_error_le
  have hs := (summable_divisorDirichletTerm (s := (3 / 2 : ℂ)) (by norm_num)).norm
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (3 / 2) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨1 + C * S, by positivity, ?_⟩
  intro t ht
  let e : ℕ → ℂ := fun n => zetaSquareDivisorContribution (-t) n / zetaSquareGammaNormalization t -
    zetaSquareLeadingDivisorContribution t n
  have hsum : HasSum e (zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t -
      zetaSquareLeadingDivisorIntegral t) :=
    ((hasSum_zetaSquareDivisorContribution (-t)).div_const _).sub
      (hasSum_zetaSquareLeadingDivisorContribution ht)
  have he : Summable (fun n => ‖e n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (hbound t ht) (hs.mul_left C)
  rw [← hsum.tsum_eq]
  calc
    _ ≤ ∑' n : ℕ, ‖e n‖ := norm_tsum_le_tsum_norm he
    _ ≤ ∑' n : ℕ, C * ‖divisorDirichletTerm (3 / 2) n‖ :=
      Summable.tsum_le_tsum (hbound t ht) he (hs.mul_left C)
    _ = C * S := tsum_mul_left
    _ ≤ _ := by linarith

end MathCollab.Density.Stronger.Atkinson
