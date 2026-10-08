module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerGapBudget

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Filter
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- The literal divisor-weighted maximal-prefix Gram budget at the original
source cutoff is bounded by the closed physical power budget. No stationary
source, local-mean excess, or moment estimate is a premise. -/
theorem exists_atkinsonPhysicalGramBudget_le_power {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → H^δ ≤ G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W ≤
        C*atkinsonPowerGapBudget η H G L
          (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,henergy⟩ := exists_atkinsonGapBudget_le_arithmetic hη
  obtain ⟨H₀,hH₀,hprefix⟩ := exists_atkinsonPhysicalPrefixGramMax_le_gap hδ
  refine ⟨C,hC,H₀,hH₀,?_⟩
  intro H G A L W hH hwidth hsep hrange hlocal
  have hH0 : 0 < H := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hH0 δ).trans_le hwidth
  let N := atkinsonSourceCutoff (2*H) G (Real.log (2*H))
  have hgap : ∀ j < Nat.clog 2 N, ∀ t ∈ W, ∀ u ∈ W,
      atkinsonPrefixGramMax (2^j) (2^j) t u ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u := by
    intro j hj t ht u hu
    exact hprefix H G hH hwidth j hj t u
      (hrange t ht).1 (hrange t ht).2 (hrange u hu).1 (hrange u hu).2
  have hnonneg : ∀ j < Nat.clog 2 N, ∀ t ∈ W, ∀ u ∈ W,
      0 ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u := by
    intro j hj t ht u hu
    exact (atkinsonPrefixGramMax_nonneg _ _ t u).trans (hgap j hj t ht u hu)
  have hdiam := atkinson_height_interval_diameter hlocal
  calc
    _ ≤ atkinsonDyadicGapBudget N W := atkinsonDyadicGramBudget_le_gapBudget N W hgap
    _ ≤ C*atkinsonArithmeticGapBudget η N W := henergy N W hnonneg
    _ ≤ C*atkinsonSeparatedGapBudget η H G N W :=
      mul_le_mul_of_nonneg_left
        (atkinsonArithmeticGapBudget_le_separated hH0 hG hsep hrange) hC.le
    _ ≤ C*atkinsonLocalizedGapBudget η H G L N W.card :=
      mul_le_mul_of_nonneg_left
        (atkinsonSeparatedGapBudget_le_localized hH0 hrange hdiam) hC.le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (atkinsonLocalizedGapBudget_le_power N W.card hH0 hG hη.le) hC.le

/-- Genuine weighted phase-prefix packets satisfy the same closed bound,
with all heights and their separate maximizing prefixes retained. -/
theorem exists_sum_atkinsonUndampedDyadicPhaseBound_sq_le_power {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → H^δ ≤ G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t
        (atkinsonSourceCutoff (2*H) G (Real.log (2*H))))^2 ≤
        C*atkinsonPowerGapBudget η H G L
          (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,H₀,hH₀,hbound⟩ := exists_atkinsonPhysicalGramBudget_le_power hδ hη
  refine ⟨C,hC,H₀,hH₀,?_⟩
  intro H G A L W hH hwidth hsep hrange hlocal
  exact (sum_atkinsonUndampedDyadicPhaseBound_sq_le_budget _ W).trans
    (hbound H G A L W hH hwidth hsep hrange hlocal)

end MathCollab.Density.Stronger.Atkinson
