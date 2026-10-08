module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNearGap
public import Mathlib.NumberTheory.Harmonic.Bounds

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

def IsSeparated (G : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → G ≤ dist x y

theorem separated_subset_card_le_one_of_diameter
    (W S : Finset ℝ) (hSep : IsSeparated 1 W) (hSW : S ⊆ W)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| < 1) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  have hlarge := hSep x (hSW hx) y (hSW hy) hxy
  exact (not_lt_of_ge hlarge) (hdiam x hx y hy)

/-- A unit-width annulus about a point contains at most one separated point on
each side. -/
theorem separated_annulus_card_le_two
    (W : Finset ℝ) (t : ℝ) (k : ℕ) (hSep : IsSeparated 1 W) :
    ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧ |u - t| < (k : ℝ) + 1}).card ≤ 2 := by
  let S := {u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧ |u - t| < (k : ℝ) + 1}
  let P : ℝ → Prop := fun u => t ≤ u
  have hpos : (S.filter P).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter W (S.filter P) hSep
    · intro u hu
      exact (Finset.mem_filter.mp hu).1 |> Finset.mem_filter.mp |>.1
    · intro x hx y hy
      have hxData := Finset.mem_filter.mp hx
      have hyData := Finset.mem_filter.mp hy
      have hxS := Finset.mem_filter.mp hxData.1
      have hyS := Finset.mem_filter.mp hyData.1
      rw [abs_of_nonneg (sub_nonneg.mpr hxData.2)] at hxS
      rw [abs_of_nonneg (sub_nonneg.mpr hyData.2)] at hyS
      rw [abs_lt]
      constructor <;> linarith [hxS.2.2, hyS.2.2]
  have hneg : (S.filter (fun u => ¬ P u)).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter W (S.filter (fun u => ¬ P u)) hSep
    · intro u hu
      exact (Finset.mem_filter.mp hu).1 |> Finset.mem_filter.mp |>.1
    · intro x hx y hy
      have hxData := Finset.mem_filter.mp hx
      have hyData := Finset.mem_filter.mp hy
      have hxS := Finset.mem_filter.mp hxData.1
      have hyS := Finset.mem_filter.mp hyData.1
      have hxt : x - t ≤ 0 := by linarith
      have hyt : y - t ≤ 0 := by linarith
      rw [abs_of_nonpos hxt] at hxS
      rw [abs_of_nonpos hyt] at hyS
      rw [abs_lt]
      constructor <;> linarith [hxS.2.2, hyS.2.2]
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) P
  change S.card ≤ 2
  omega

/-- The reciprocal distances from one point to the other separated points in
its `N`-neighborhood have harmonic, rather than linear, total mass. -/
theorem sum_inv_distance_near_le_harmonic
    (N : ℕ) (W : Finset ℝ) (t : ℝ) (hSep : IsSeparated 1 W) (ht : t ∈ W) :
    (∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}, 1 / |u - t|) ≤
      2 * (((harmonic N : ℚ) : ℝ)) := by
  let S := {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}
  let shell : ℝ → ℕ := fun u => Nat.floor |u - t|
  have hmaps : ∀ u ∈ S, shell u ∈ Finset.Icc 1 N := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    have hu := huData.1
    have hne := huData.2.1
    have hsep := hSep t ht u hu (Ne.symm hne)
    have hqOne : 1 ≤ |u - t| := by simpa only [Real.dist_eq, abs_sub_comm] using hsep
    have hqNonneg : 0 ≤ |u - t| := abs_nonneg _
    have hfloorPos : 0 < shell u := by
      exact Nat.floor_pos.mpr hqOne
    have hfloorLeReal : ((shell u : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact (Nat.floor_le hqNonneg).trans huData.2.2
    have hfloorLe : shell u ≤ N := by exact_mod_cast hfloorLeReal
    exact Finset.mem_Icc.mpr ⟨hfloorPos, hfloorLe⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun u => 1 / |u - t|)]
  calc
    (∑ k ∈ Finset.Icc 1 N, ∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
        ∑ k ∈ Finset.Icc 1 N, 2 * (1 / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := (Finset.mem_Icc.mp hk).1
      have hfiberCard : ({u ∈ S | shell u = k}).card ≤ 2 := by
        calc
          ({u ∈ S | shell u = k}).card ≤
              ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧
                |u - t| < (k : ℝ) + 1}).card := by
            apply Finset.card_le_card
            intro u hu
            have huData := Finset.mem_filter.mp hu
            have huS := Finset.mem_filter.mp huData.1
            have hfloor := huData.2
            have hqNonneg : 0 ≤ |u - t| := abs_nonneg _
            have hlow : (k : ℝ) ≤ |u - t| := by
              rw [← hfloor]
              exact Nat.floor_le hqNonneg
            have hhigh : |u - t| < (k : ℝ) + 1 := by
              rw [← hfloor]
              exact Nat.lt_floor_add_one _
            exact Finset.mem_filter.mpr ⟨huS.1, huS.2.1, hlow, hhigh⟩
          _ ≤ 2 := separated_annulus_card_le_two W t k hSep
      calc
        (∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
            ∑ u ∈ S with shell u = k, 1 / (k : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          have huData := Finset.mem_filter.mp hu
          have huS := Finset.mem_filter.mp huData.1
          have hfloor := huData.2
          have hqNonneg : 0 ≤ |u - t| := abs_nonneg _
          have hkq : (k : ℝ) ≤ |u - t| := by
            rw [← hfloor]
            exact Nat.floor_le hqNonneg
          exact one_div_le_one_div_of_le (by exact_mod_cast hkPos) hkq
        _ = (({u ∈ S | shell u = k}).card : ℝ) * (1 / (k : ℝ)) := by simp
        _ ≤ 2 * (1 / (k : ℝ)) := by
          gcongr
          exact_mod_cast hfiberCard
    _ = 2 * (((harmonic N : ℚ) : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [inv_eq_one_div]
      rw [Finset.mul_sum]


end MathCollab.Density.Stronger.Atkinson
