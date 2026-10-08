module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightReflection

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


def zetaDivisorWeightArgument (t : ℝ) (n : ℕ) : ℂ :=
  (Real.log (n : ℝ) : ℂ) - zetaGammaLeadingLog t

theorem zetaDivisorWeightArgument_re (t : ℝ) (n : ℕ) :
    (zetaDivisorWeightArgument t n).re = Real.log (n : ℝ) - Real.log (t / (2 * Real.pi)) := by
  simp only [zetaDivisorWeightArgument, zetaGammaLeadingLog, sub_re, ofReal_re,
    mul_re, ofReal_im, I_re, I_im, zero_mul, mul_zero, sub_zero]

theorem zetaDivisorWeightArgument_im (t : ℝ) (n : ℕ) :
    (zetaDivisorWeightArgument t n).im = Real.pi / 2 := by
  simp only [zetaDivisorWeightArgument, zetaGammaLeadingLog, sub_im, ofReal_im,
    mul_im, ofReal_re, I_re, I_im, zero_mul, mul_one, add_zero, zero_sub, neg_neg]

theorem divisorDirichletTerm_add_eq_mul_exp (s w : ℂ) (n : ℕ) :
    divisorDirichletTerm (s + w) n =
      divisorDirichletTerm s n * Complex.exp (-((Real.log (n : ℝ) : ℂ)) * w) := by
  by_cases hn : n = 0
  · subst n
    simp [divisorDirichletTerm, LSeries.term]
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    divisorDirichletTerm_eq_divisorWeight_mul_cpow, neg_add,
    Complex.cpow_add _ _ hne, Complex.cpow_def_of_ne_zero hne (-w), hlog]
  rw [show ((Real.log (n : ℝ) : ℂ)) * -w = -((Real.log (n : ℝ) : ℂ)) * w by ring]
  ring

theorem zetaSquareLeadingDivisorTerm_eq_weightKernel (t : ℝ) (n : ℕ) (u : ℝ) :
    zetaSquareLeadingDivisorTerm t n u =
      (divisorDirichletTerm (afeCriticalPoint (-t)) n * zetaSquareReflectedGammaPhase t) *
        zetaDivisorWeightKernel (zetaDivisorWeightArgument t n) (1 + (u : ℂ) * I) := by
  unfold zetaSquareLeadingDivisorTerm
  rw [divisorDirichletTerm_add_eq_mul_exp]
  unfold zetaSquareLeadingRightKernel zetaDivisorWeightKernel zetaDivisorWeightNumerator
    zetaDivisorWeightArgument
  dsimp only
  rw [show -((Real.log (n : ℝ) : ℂ) - zetaGammaLeadingLog t) * (1 + (u : ℂ) * I) =
      -((Real.log (n : ℝ) : ℂ)) * (1 + (u : ℂ) * I) +
        (1 + (u : ℂ) * I) * zetaGammaLeadingLog t by ring, Complex.exp_add]
  ring

theorem zetaSquareLeadingDivisorContribution_eq_weight (t : ℝ) (n : ℕ) :
    zetaSquareLeadingDivisorContribution t n =
      divisorDirichletTerm (afeCriticalPoint (-t)) n * zetaSquareReflectedGammaPhase t *
        zetaDivisorWeight (zetaDivisorWeightArgument t n) := by
  unfold zetaSquareLeadingDivisorContribution zetaDivisorWeight
  simp_rw [zetaSquareLeadingDivisorTerm_eq_weightKernel, integral_const_mul]
  ring

/-- The complete source series is the actual oscillatory divisor series
with the identified complex weight, including its zero coefficient. -/
theorem hasSum_zetaSquareLeadingDivisor_weighted {t : ℝ} (ht : 4 ≤ t) :
    HasSum (fun n : ℕ => divisorDirichletTerm (afeCriticalPoint (-t)) n *
      zetaSquareReflectedGammaPhase t * zetaDivisorWeight (zetaDivisorWeightArgument t n))
      (zetaSquareLeadingDivisorIntegral t) := by
  convert hasSum_zetaSquareLeadingDivisorContribution ht using 1
  funext n
  exact (zetaSquareLeadingDivisorContribution_eq_weight t n).symm

theorem exp_neg_zetaDivisorWeightArgument_re {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 0 < n) :
    Real.exp (-(zetaDivisorWeightArgument t n).re) = t / (2 * Real.pi * (n : ℝ)) := by
  rw [zetaDivisorWeightArgument_re, neg_sub, Real.exp_sub,
    Real.exp_log (by positivity), Real.exp_log (by positivity)]
  ring

/-- One constant for all physical heights and positive divisor indices.
In particular the small-index weight is uniformly bounded, not `O(t/n)`. -/
theorem exists_norm_source_zetaDivisorWeight_min_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ n : ℕ, 0 < n →
      ‖zetaDivisorWeight (zetaDivisorWeightArgument t n)‖ ≤
        C * min 1 (t / (2 * Real.pi * (n : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaDivisorWeight_min_le
    (B := Real.pi / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro t ht n hn
  have h := hbound (zetaDivisorWeightArgument t n)
    (by rw [zetaDivisorWeightArgument_im, abs_of_pos (by positivity)])
  rwa [exp_neg_zetaDivisorWeightArgument_re ht hn] at h

end MathCollab.Density.Stronger.Atkinson
