module
-- Reversible module-visibility port of the audited development.
/-
Literal Heath--Brown Lemma 3 statement and coordinate bridge adapted from
Scott McColm, PointMeanLemmaThreeStatement.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The proposition is a definition; no instance is assumed.
-/
public import MathCollab.Density.Stronger.CriticalMoment

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Finset MeasureTheory
open scoped BigOperators Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

private theorem statement_intervalIntegrable_exp_neg_abs_sub_mul
    (f : ℝ → ℝ) (hf : Continuous f) (t a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => Real.exp (-|t-v|) * f v) volume a b :=
  ((by fun_prop : Continuous (fun v : ℝ => Real.exp (-|t-v|))).mul hf).intervalIntegrable _ _

/-- The truncated exponentially weighted critical-line second moment in the
coordinates printed in Heath--Brown's Lemma 3. -/
noncomputable def heathBrownLemmaThreeMoment (t L : ℝ) : ℝ :=
  ∫ u in -L..L,
    Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

/-- Heath--Brown (1978), Lemma 3, with an explicit absolute constant. -/
def HeathBrownLemmaThree : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 10 ≤ t →
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t *
          (1 + heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)))

/-- Translation from the source's increment coordinate `u` to the physical
ordinate coordinate.  This is an exact identity with the literal
exponential kernel. -/
theorem heathBrownLemmaThreeMoment_eq_centered (t L : ℝ) :
    heathBrownLemmaThreeMoment t L =
      ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) := by
  let f : ℝ → ℝ := fun v ↦
    Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ)
  have hshift := intervalIntegral.integral_comp_add_right f t
      (a := -L) (b := L)
  unfold heathBrownLemmaThreeMoment
  calc
    (∫ u in -L..L,
        Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) =
        ∫ u in -L..L, f (u + t) := by
      apply intervalIntegral.integral_congr
      intro u hu
      simp only [f, show t - (u + t) = -u by ring, abs_neg]
      rw [add_comm]
    _ = ∫ v in -L + t..L + t, f v := hshift
    _ = ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) := by
      congr 1 <;> ring

/-- A source Lemma-3 moment may be enlarged to any symmetric radius which
dominates `(log t)^2`. -/
theorem heathBrownLemmaThreeMoment_le_centered
    (t L : ℝ) (hlogL : Real.log t ^ (2 : ℕ) ≤ L) :
    heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)) ≤
      ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) := by
  rw [heathBrownLemmaThreeMoment_eq_centered]
  apply intervalIntegral.integral_mono_interval
  · linarith
  · nlinarith [sq_nonneg (Real.log t)]
  · linarith
  · filter_upwards with v
    positivity
  · exact statement_intervalIntegrable_exp_neg_abs_sub_mul
      (fun v : ℝ ↦ zetaMomentCriticalNorm v ^ (2 : ℕ))
      (continuous_zetaMomentCriticalNorm.pow 2) t (t - L) (t + L)

end MathCollab.Density.Stronger.PointMean
