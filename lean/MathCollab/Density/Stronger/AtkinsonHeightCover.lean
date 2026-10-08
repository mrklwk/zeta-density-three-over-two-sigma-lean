module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.AtkinsonCardinalityAbsorption

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from Scott McColm, source commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
McColm source: MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
The localized packet bound remains an explicit theorem hypothesis.
No physical Atkinson estimate or point-mean theorem is imported or asserted.
-/

set_option autoImplicit false

/-!
# Constructed localization of a physical height set

Floor bins partition the actual set in [H,2H]. Every fiber inherits
its real location; the terminal endpoint belongs to the final bin.
-/

noncomputable section

namespace MathCollab.Density.Stronger

def atkinsonHeightBin (H L t : ℝ) : ℕ :=
  Nat.floor ((t-H)/L)

def atkinsonHeightFiber (H L : ℝ) (W : Finset ℝ) (k : ℕ) : Finset ℝ :=
  W.filter (fun t => atkinsonHeightBin H L t = k)

theorem atkinsonHeightFiber_subset (H L : ℝ) (W : Finset ℝ) (k : ℕ) :
    atkinsonHeightFiber H L W k ⊆ W :=
  Finset.filter_subset _ W

theorem atkinsonHeightBin_mem_range {H L t : ℝ}
    (hL : 0 < L) (ht : t ≤ 2*H) :
    atkinsonHeightBin H L t ∈ Finset.range (Nat.floor (H/L)+1) := by
  have hq : (t-H)/L ≤ H/L :=
    div_le_div_of_nonneg_right (by linarith) hL.le
  have hf := Nat.floor_mono hq
  simp only [atkinsonHeightBin,Finset.mem_range]
  omega

theorem atkinsonHeightFiber_interval {H L : ℝ} {W : Finset ℝ} (k : ℕ)
    (hL : 0 < L) (hrange : ∀ t ∈ W, H ≤ t) :
    ∀ t ∈ atkinsonHeightFiber H L W k,
      H+(k:ℝ)*L ≤ t ∧ t ≤ (H+(k:ℝ)*L)+L := by
  intro t ht
  obtain ⟨htW,htbin⟩ := Finset.mem_filter.mp ht
  have hq : 0 ≤ (t-H)/L := div_nonneg (sub_nonneg.mpr (hrange t htW)) hL.le
  have hlo := Nat.floor_le hq
  have hhi := Nat.lt_floor_add_one ((t-H)/L)
  change (atkinsonHeightBin H L t:ℝ) ≤ (t-H)/L at hlo
  change (t-H)/L < (atkinsonHeightBin H L t:ℝ)+1 at hhi
  rw [htbin] at hlo hhi
  have hl := (le_div_iff₀ hL).mp hlo
  have hh := (div_lt_iff₀ hL).mp hhi
  constructor <;> nlinarith

theorem atkinsonHeightFiber_card_partition {H L : ℝ} (W : Finset ℝ)
    (hL : 0 < L) (hrange : ∀ t ∈ W, t ≤ 2*H) :
    W.card = ∑ k ∈ Finset.range (Nat.floor (H/L)+1),
      (atkinsonHeightFiber H L W k).card := by
  exact Finset.card_eq_sum_card_fiberwise
    (fun t ht => atkinsonHeightBin_mem_range hL (hrange t ht))

theorem atkinson_card_le_of_height_fibers {H L B : ℝ} {W : Finset ℝ}
    (hL : 0 < L) (hrange : ∀ t ∈ W, t ≤ 2*H)
    (hcard : ∀ k ∈ Finset.range (Nat.floor (H/L)+1),
      ((atkinsonHeightFiber H L W k).card:ℝ) ≤ B) :
    (W.card:ℝ) ≤ ((Nat.floor (H/L)+1:ℕ):ℝ)*B := by
  have he : (W.card:ℝ) = ∑ k ∈ Finset.range (Nat.floor (H/L)+1),
      ((atkinsonHeightFiber H L W k).card:ℝ) := by
    exact_mod_cast atkinsonHeightFiber_card_partition W hL hrange
  rw [he]
  calc
    _ ≤ ∑ _k ∈ Finset.range (Nat.floor (H/L)+1), B := Finset.sum_le_sum hcard
    _ = _ := by simp

end MathCollab.Density.Stronger
