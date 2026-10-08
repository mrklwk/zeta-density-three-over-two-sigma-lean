module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.LargeValueDefinitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from Scott McColm, source commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
McColm source: MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
This module imports only the displayed local/mathlib dependencies, not the upstream project.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem exists_unitSeparated_closedBall_cover_of_card_bound
    {S : Set ℝ} {B : ℝ}
    (hcount : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      oneSeparated W → (W.card:ℝ) ≤ B) :
    ∃ W : Finset ℝ, (∀ t ∈ W, t ∈ S) ∧ oneSeparated W ∧
      ∀ t ∈ S, ∃ u ∈ W, dist t u ≤ 1 := by
  classical
  let N : ℕ := Nat.ceil B
  let Q : Finset ℕ := (Finset.range (N+1)).filter (fun n =>
    ∃ W : Finset ℝ, (∀ t ∈ W, t ∈ S) ∧ oneSeparated W ∧ W.card = n)
  have hN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hmem : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      oneSeparated W → W.card ∈ Q := by
    intro W hWS hsep
    have hcard : W.card ≤ N := by exact_mod_cast (hcount W hWS hsep).trans hN
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),W,hWS,hsep,rfl⟩
  have hzero : 0 ∈ Q := by
    simpa using hmem ∅ (by simp) (by intro x hx; simp at hx)
  have hQ : Q.Nonempty := ⟨0,hzero⟩
  obtain ⟨W,hWS,hsep,hcard⟩ := (Finset.mem_filter.mp (Q.max'_mem hQ)).2
  refine ⟨W,hWS,hsep,?_⟩
  intro t ht
  by_contra hnot
  have hfar : ∀ u ∈ W, 1 < dist t u := by
    intro u hu
    exact lt_of_not_ge (fun h => hnot ⟨u,hu,h⟩)
  have htW : t ∉ W := by
    intro htW
    have hh := hfar t htW
    norm_num at hh
  have hWS' : ∀ u ∈ insert t W, u ∈ S := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ht
    · exact hWS u hu
  have hsep' : oneSeparated (insert t W) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hxW
    · rcases Finset.mem_insert.mp hy with rfl | hyW
      · exact (hxy rfl).elim
      · simpa only [Real.dist_eq] using (hfar y hyW).le
    · rcases Finset.mem_insert.mp hy with rfl | hyW
      · simpa only [dist_comm, Real.dist_eq] using (hfar x hxW).le
      · exact hsep x hxW y hyW hxy
  have hmax : (insert t W).card ≤ Q.max' hQ :=
    Q.le_max' (insert t W).card (hmem (insert t W) hWS' hsep')
  rw [Finset.card_insert_of_notMem htW,← hcard] at hmax
  omega

theorem volume_le_two_mul_of_separated_card_bound
    {S : Set ℝ} {B : ℝ}
    (hcount : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      oneSeparated W → (W.card:ℝ) ≤ B) :
    volume S ≤ ENNReal.ofReal (2*B) := by
  classical
  obtain ⟨W,hWS,hsep,hcover⟩ :=
    exists_unitSeparated_closedBall_cover_of_card_bound hcount
  have hsub : S ⊆ ⋃ u ∈ W, Metric.closedBall u 1 := by
    intro t ht
    obtain ⟨u,hu,hut⟩ := hcover t ht
    exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hut⟩⟩
  calc
    volume S ≤ volume (⋃ u ∈ W, Metric.closedBall u 1) := measure_mono hsub
    _ ≤ ∑ u ∈ W, volume (Metric.closedBall u 1) := measure_biUnion_finset_le W _
    _ = (W.card:ℝ≥0∞)*2 := by simp [Real.volume_closedBall]
    _ = ENNReal.ofReal (2*(W.card:ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp [mul_comm]
    _ ≤ ENNReal.ofReal (2*B) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcount W hWS hsep) (by norm_num))


end MathCollab.Density.Stronger
