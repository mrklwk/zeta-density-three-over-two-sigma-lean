module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNearGapBudget
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFarGap

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

theorem atkinson_far_gap_row_le {H L : ℝ} {M : ℕ} {W : Finset ℝ} {t : ℝ}
    (hH : 0 < H) (hM : 0 < M) (ht : t ∈ W)
    (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H)
    (hdiam : ∀ u ∈ W, |u-t| ≤ L) :
    atkinsonFarGapRow H M W t ≤
      (W.card:ℝ)*(2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ)))) := by
  classical
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hR : 0 < Real.sqrt (H*(M:ℝ)) := by positivity
  let S := W.filter (fun u => Real.sqrt (H*(M:ℝ)) < |u-t|)
  have hbound : ∀ u ∈ S, atkinsonPrefixGapMajorant M M t u ≤
      2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ))) := by
    intro u hu
    have hd := Finset.mem_filter.mp hu
    have hf := atkinsonPrefixGapMajorant_le_far hH
      (hrange t ht).1 (hrange t ht).2 (hrange u hd.1).1 (hrange u hd.1).2 hM
      (by simpa only [abs_sub_comm] using hd.2.le)
    have hmono : (M:ℝ)*|t-u|/Real.sqrt (H*(M:ℝ)) ≤
        (M:ℝ)*L/Real.sqrt (H*(M:ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by simpa only [abs_sub_comm] using hdiam u hd.1) hM0.le) hR.le
    exact hf.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num))
  calc
    _ ≤ ∑ u ∈ S, 2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ))) :=
      Finset.sum_le_sum hbound
    _ = (S.card:ℝ)*(2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ)))) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (Finset.filter_subset (s := W) _))
      (by positivity)

theorem atkinson_far_gap_double_sum_le {H L : ℝ} {M : ℕ} {W : Finset ℝ}
    (hH : 0 < H) (hM : 0 < M)
    (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H)
    (hdiam : ∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) :
    (∑ t ∈ W, atkinsonFarGapRow H M W t) ≤
      (W.card:ℝ)^2*(2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ)))) := by
  calc
    _ ≤ ∑ t ∈ W, (W.card:ℝ)*(2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ)))) :=
      Finset.sum_le_sum (fun t ht => atkinson_far_gap_row_le hH hM ht hrange (hdiam t ht))
    _ = _ := by simp; ring

def atkinsonLocalizedGapBudget (η H G L : ℝ) (N R : ℕ) : ℝ :=
  (Nat.clog 2 N:ℝ)*∑ j ∈ Finset.range (Nat.clog 2 N),
    (((2^j:ℕ):ℝ)^(1/2+η))*
      ((R:ℝ)*atkinsonNearRowBound H G (2^j)+
        (R:ℝ)^2*(2000*Real.sqrt (((2^j:ℕ):ℝ)*L/Real.sqrt (H*((2^j:ℕ):ℝ)))))

theorem atkinsonLocalizedGapBudget_zero_card (η H G L : ℝ) (N : ℕ) :
    atkinsonLocalizedGapBudget η H G L N 0 = 0 := by
  simp [atkinsonLocalizedGapBudget]

theorem atkinsonSeparatedGapBudget_le_localized {H G L η : ℝ} {N : ℕ} {W : Finset ℝ}
    (hH : 0 < H) (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H)
    (hdiam : ∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) :
    atkinsonSeparatedGapBudget η H G N W ≤
      atkinsonLocalizedGapBudget η H G L N W.card := by
  unfold atkinsonSeparatedGapBudget atkinsonLocalizedGapBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := atkinson_far_gap_double_sum_le (M := 2^j) hH (pow_pos (by norm_num) _) hrange hdiam
  linarith

theorem atkinson_height_interval_diameter {A L : ℝ} {W : Finset ℝ}
    (hlocal : ∀ t ∈ W, A ≤ t ∧ t ≤ A+L) :
    ∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L := by
  intro t ht u hu
  rw [abs_le]
  constructor <;> linarith [(hlocal t ht).1,(hlocal t ht).2,(hlocal u hu).1,(hlocal u hu).2]
end MathCollab.Density.Stronger.Atkinson
