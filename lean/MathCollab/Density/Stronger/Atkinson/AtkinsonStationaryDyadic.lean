module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryBlockBound
public import MathCollab.Density.Stronger.Atkinson.AtkinsonDampedDyadic
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonStationaryLeadingFiniteSum_eq_dyadic (T G L : ℝ) (N : ℕ) :
    atkinsonStationaryLeadingFiniteSum T G L N =
      ∑ j ∈ Finset.range (Nat.clog 2 N),
        atkinsonStationaryBlock T G L (2^j) (truncatedDyadicLength N j) :=
  sum_range_eq_truncatedDyadic (atkinsonStationaryLeadingTerm T G L)
    (atkinsonStationaryLeadingTerm_zero T G L) N

theorem norm_atkinsonStationaryLeadingFiniteSum_le_blocks (T G L : ℝ) (N : ℕ) :
    ‖atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
      ∑ j ∈ Finset.range (Nat.clog 2 N),
        ‖atkinsonStationaryBlock T G L (2^j) (truncatedDyadicLength N j)‖ := by
  rw [atkinsonStationaryLeadingFiniteSum_eq_dyadic]
  exact norm_sum_le _ _

theorem exists_norm_atkinsonStationaryFiniteSum_le_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T → 0 < L →
      ∀ N : ℕ, 10000*(N:ℝ) ≤ T →
      ‖atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
        C*G*T^(-(1/4:ℝ))*atkinsonDyadicPhaseBound T G N := by
  obtain ⟨C,hC,hblock⟩ := exists_norm_atkinsonStationaryBlock_le
  refine ⟨C,hC,?_⟩
  intro T G L hT hG hGT hL N hN
  apply (norm_atkinsonStationaryLeadingFiniteSum_le_blocks T G L N).trans
  unfold atkinsonDyadicPhaseBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have he : (((2^j+truncatedDyadicLength N j):ℕ):ℝ) ≤ N := by
    exact_mod_cast truncatedDyadic_endpoint_le (Finset.mem_range.mp hj)
  apply (hblock T G L hT hG hGT hL (2^j) (truncatedDyadicLength N j)
    (pow_pos (by norm_num) _) (by linarith)).trans_eq
  ring

theorem exists_norm_atkinsonStationarySum_le_dyadic {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T)) := by
  obtain ⟨C,hC,A,hA,hblock⟩ := exists_atkinsonSourceCutoff_block_bound hδ
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_zetaSmoothDivisorTest_support_physical hδ)
  refine ⟨C,hC,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  obtain ⟨hG,hL,hwidth,_⟩ := (hB T hBT).2 G hlower
  rw [atkinsonStationaryLeadingSum_eq_finite hT0 hG hL hwidth]
  apply (norm_atkinsonStationaryLeadingFiniteSum_le_blocks T G (Real.log T) _).trans
  unfold atkinsonDyadicPhaseBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply (hblock T G hAT hlower hupper (2^j) _
    (pow_pos (by norm_num) _) (truncatedDyadic_endpoint_le (Finset.mem_range.mp hj))).trans_eq
  ring

theorem exists_norm_atkinsonStationarySum_le_fullDyadic {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T)) := by
  obtain ⟨C,hC,A,hA,hbound⟩ := exists_norm_atkinsonStationarySum_le_dyadic hδ
  refine ⟨C,hC,A,hA,?_⟩
  intro T G hT hlower hupper
  have hT0 : 0 < T := by linarith [hA.trans hT]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  exact (hbound T G hT hlower hupper).trans (mul_le_mul_of_nonneg_left
    (atkinsonDyadicPhaseBound_le_full T G _) (by positivity))

/-- The complete literal stationary source is controlled by native undamped phase prefixes. -/
theorem exists_norm_atkinsonStationarySum_le_undamped {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonUndampedDyadicPhaseBound T (atkinsonSourceCutoff T G (Real.log T)) := by
  obtain ⟨C,hC,T₀,hT₀,hbound⟩ := exists_norm_atkinsonStationarySum_le_fullDyadic hδ
  refine ⟨C,hC,T₀,hT₀,?_⟩
  intro T G hT hlower hupper
  have hT0 : 0 < T := by linarith [hT₀.trans hT]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  exact (hbound T G hT hlower hupper).trans (mul_le_mul_of_nonneg_left
    (atkinsonFullDyadicPhaseBound_le_undamped hT0 G _) (by positivity))

end MathCollab.Density.Stronger.Atkinson
