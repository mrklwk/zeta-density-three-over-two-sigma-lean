module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonDyadicGramBudget

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonDyadicGapBudget (N : ℕ) (W : Finset ℝ) : ℝ :=
  (Nat.clog 2 N : ℝ)*∑ j ∈ Finset.range (Nat.clog 2 N),
    (((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*atkinsonBlockCoefficientEnergy (2^j) (2^j)*
      ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant (2^j) (2^j) t u

theorem atkinsonDyadicGramBudget_le_gapBudget (N : ℕ) (W : Finset ℝ)
    (hgap : ∀ j < Nat.clog 2 N, ∀ t ∈ W, ∀ u ∈ W,
      atkinsonPrefixGramMax (2^j) (2^j) t u ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u) :
    atkinsonDyadicGramBudget N W ≤ atkinsonDyadicGapBudget N W := by
  unfold atkinsonDyadicGramBudget atkinsonDyadicGapBudget
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (sq_nonneg _) (atkinsonBlockCoefficientEnergy_nonneg _ _))
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro u hu
  exact hgap j (Finset.mem_range.mp hj) t ht u hu

theorem atkinsonDyadicGapBudget_empty (N : ℕ) :
    atkinsonDyadicGapBudget N ∅ = 0 := by
  simp [atkinsonDyadicGapBudget]

theorem atkinsonDyadicGapBudget_zero (W : Finset ℝ) :
    atkinsonDyadicGapBudget 0 W = 0 := by
  simp [atkinsonDyadicGapBudget]

theorem exists_atkinsonPhysicalGramBudget_le_gapBudget {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G) →
      atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W ≤
        atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨A,hA,hgap⟩ := exists_atkinsonPhysicalPrefixGramMax_le_gap hδ
  refine ⟨A,hA,?_⟩
  intro H G W hH hrange
  by_cases hW : W = ∅
  · subst W
    simp [atkinsonDyadicGramBudget,atkinsonDyadicGapBudget]
  · obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr hW
    have hH0 : 0 < H := by linarith [hA.trans hH]
    have hwidth : H^δ ≤ G :=
      (Real.rpow_le_rpow hH0.le (hrange v hv).1 hδ.le).trans (hrange v hv).2.2
    apply atkinsonDyadicGramBudget_le_gapBudget
    intro j hj t ht u hu
    exact hgap H G hH hwidth j hj t u (hrange t ht).1 (hrange t ht).2.1
      (hrange u hu).1 (hrange u hu).2.1
end MathCollab.Density.Stronger.Atkinson
