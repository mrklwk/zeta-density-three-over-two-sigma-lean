module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.SeparatedReciprocal

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

theorem atkinson_isSeparated_div {G : ℝ} {W : Finset ℝ}
    (hG : 0 < G) (hSep : IsSeparated G W) :
    IsSeparated 1 (W.image (fun t => t/G)) := by
  classical
  intro x hx y hy hne
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
  have htu : t ≠ u := fun h => hne (by rw [h])
  have hs := hSep t ht u hu htu
  rw [Real.dist_eq] at hs ⊢
  rw [← sub_div, abs_div, abs_of_pos hG]
  exact (le_div_iff₀ hG).mpr (by simpa using hs)

theorem atkinson_sum_inv_gap_le_harmonic {G : ℝ} {W S : Finset ℝ} {t : ℝ}
    (N : ℕ) (hG : 0 < G) (hSep : IsSeparated G W) (ht : t ∈ W)
    (hSW : S ⊆ W) (hnear : ∀ u ∈ S, u ≠ t ∧ |u-t| ≤ G*(N:ℝ)) :
    (∑ u ∈ S, 1/|u-t|) ≤ (2/G)*(harmonic N:ℝ) := by
  classical
  let V := W.image (fun u => u/G)
  let A := S.image (fun u => u/G)
  have hinj : Function.Injective (fun u : ℝ => u/G) :=
    fun _ _ h => (div_left_inj' hG.ne').mp h
  have hAV : A ⊆ {v ∈ V | v ≠ t/G ∧ |v-t/G| ≤ (N:ℝ)} := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨u,hSW hu,rfl⟩,?_,?_⟩
    · exact fun h => (hnear u hu).1 (hinj h)
    · rw [← sub_div, abs_div, abs_of_pos hG]
      exact (div_le_iff₀ hG).mpr (by simpa [mul_comm] using (hnear u hu).2)
  have hs := sum_inv_distance_near_le_harmonic N V (t/G)
    (atkinson_isSeparated_div hG hSep) (Finset.mem_image.mpr ⟨t,ht,rfl⟩)
  have hsub : (∑ v ∈ A, 1/|v-t/G|) ≤
      ∑ v ∈ {v ∈ V | v ≠ t/G ∧ |v-t/G| ≤ (N:ℝ)}, 1/|v-t/G| :=
    Finset.sum_le_sum_of_subset_of_nonneg hAV (fun _ _ _ => by positivity)
  have heq : (∑ v ∈ A, 1/|v-t/G|) = G*∑ u ∈ S, 1/|u-t| := by
    dsimp only [A]
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← sub_div, abs_div, abs_of_pos hG]
    field_simp
  rw [heq] at hsub
  have h := hsub.trans hs
  calc
    _ ≤ (2*(harmonic N:ℝ))/G := (le_div_iff₀ hG).mpr (by simpa [mul_comm] using h)
    _ = _ := by ring

theorem atkinson_sum_inv_gap_le_harmonic_ceil {G L : ℝ} {W S : Finset ℝ} {t : ℝ}
    (hG : 0 < G) (hSep : IsSeparated G W) (ht : t ∈ W)
    (hSW : S ⊆ W) (hnear : ∀ u ∈ S, u ≠ t ∧ |u-t| ≤ L) :
    (∑ u ∈ S, 1/|u-t|) ≤ (2/G)*(harmonic (Nat.ceil (L/G)):ℝ) := by
  apply atkinson_sum_inv_gap_le_harmonic (Nat.ceil (L/G)) hG hSep ht hSW
  intro u hu
  refine ⟨(hnear u hu).1,(hnear u hu).2.trans ?_⟩
  have h := Nat.le_ceil (L/G)
  have hm := mul_le_mul_of_nonneg_left h hG.le
  field_simp at hm
  exact hm
end MathCollab.Density.Stronger.Atkinson
