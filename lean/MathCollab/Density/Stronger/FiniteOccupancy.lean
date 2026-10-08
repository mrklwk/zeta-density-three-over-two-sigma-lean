module
-- Reversible module-visibility port of the audited development.
public import Mathlib.Analysis.PSeries
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

set_option autoImplicit false

/-!
# Exact occupancy recovery from finite superlevels

Summing all positive occupancy levels recovers every original point.
An inverse-square superlevel bound is summable without any loss
depending on the maximal occupancy or the physical cluster width.
-/

noncomputable section

open Finset

namespace MathCollab.Density.Stronger

theorem sum_nat_occupancy_eq_sum_superlevel
    {α : Type*} (S : Finset α) (f : α → ℕ) (M : ℕ)
    (hM : ∀ x ∈ S, f x ≤ M) :
    ∑ x ∈ S, f x =
      ∑ m ∈ Finset.Icc 1 M, (S.filter (fun x => m ≤ f x)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hf : (Finset.Icc 1 M).filter (fun m => m ≤ f x) =
      Finset.Icc 1 (f x) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have := hM x hx
    omega
  rw [← Finset.sum_filter, hf]
  simp

theorem sum_pos_nat_inv_sq_le_two (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, ((m : ℝ)^2)⁻¹) ≤ 2 := by
  have hI : Finset.Icc 1 M = Finset.Ioo 0 (M+1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hI]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (M+1))

theorem sum_nat_occupancy_le_of_superlevels
    {α : Type*} (S : Finset α) (f : α → ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hcount : ∀ m : ℕ, 0 < m →
      ((S.filter (fun x => m ≤ f x)).card : ℝ) ≤ B / (m : ℝ)^2) :
    ((∑ x ∈ S, f x) : ℝ) ≤ 2*B := by
  classical
  let M : ℕ := S.sup f
  have hM : ∀ x ∈ S, f x ≤ M := fun x hx => Finset.le_sup hx
  have he := sum_nat_occupancy_eq_sum_superlevel S f M hM
  have heReal : ((∑ x ∈ S, f x) : ℝ) =
      ∑ m ∈ Finset.Icc 1 M, ((S.filter (fun x => m ≤ f x)).card : ℝ) := by
    exact_mod_cast he
  rw [heReal]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 M, B / (m : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact hcount m (by have := (Finset.mem_Icc.mp hm).1; omega)
    _ = B * ∑ m ∈ Finset.Icc 1 M, ((m : ℝ)^2)⁻¹ := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ B*2 := mul_le_mul_of_nonneg_left (sum_pos_nat_inv_sq_le_two M) hB
    _ = 2*B := by ring

end MathCollab.Density.Stronger
