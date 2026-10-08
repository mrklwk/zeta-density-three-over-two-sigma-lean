module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalizedPowers

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

theorem atkinson_harmonic_mono {m n : ℕ} (hmn : m ≤ n) :
    (harmonic m:ℝ) ≤ (harmonic n:ℝ) := by
  unfold harmonic
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => by positivity)

def atkinsonPowerGapTerm (η H G L : ℝ) (N R : ℕ) : ℝ :=
  (R:ℝ)*(N:ℝ)^(3/2+η)+
    (120*(R:ℝ)*Real.sqrt H/G)*(N:ℝ)^(1+η)*
      (harmonic (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)):ℝ)+
    (2000*(R:ℝ)^2*H^(-(1/4:ℝ))*Real.sqrt L)*(N:ℝ)^(3/4+η)

def atkinsonPowerGapBudget (η H G L : ℝ) (N R : ℕ) : ℝ :=
  (Nat.clog 2 N:ℝ)^2*atkinsonPowerGapTerm η H G L N R

theorem atkinson_localized_gap_term_eq {H : ℝ} {M : ℕ}
    (hH : 0 < H) (hM : 0 < M) (η G L : ℝ) (R : ℕ) :
    (M:ℝ)^(1/2+η)*((R:ℝ)*atkinsonNearRowBound H G M+
      (R:ℝ)^2*(2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ))))) =
        atkinsonPowerGapTerm η H G L M R := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  unfold atkinsonNearRowBound atkinsonPowerGapTerm
  calc
    _ = (R:ℝ)*((M:ℝ)^(1/2+η)*(M:ℝ))+
        (120*(R:ℝ)/G)*((M:ℝ)^(1/2+η)*Real.sqrt (H*(M:ℝ)))*
          (harmonic (Nat.ceil (Real.sqrt (H*(M:ℝ))/G)):ℝ)+
        (2000*(R:ℝ)^2)*((M:ℝ)^(1/2+η)*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ)))) := by ring
    _ = _ := by
      rw [atkinson_weighted_diagonal_power hM0,
        atkinson_weighted_near_power hH hM0,atkinson_weighted_far_power hH hM0]
      ring

theorem atkinsonPowerGapTerm_mono_index {H G η L : ℝ} {M N : ℕ} (R : ℕ)
    (hH : 0 < H) (hG : 0 < G) (hη : 0 ≤ η) (hM : 0 < M) (hMN : M ≤ N) :
    atkinsonPowerGapTerm η H G L M R ≤ atkinsonPowerGapTerm η H G L N R := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hMN0 : (M:ℝ) ≤ N := by exact_mod_cast hMN
  have hd := Real.rpow_le_rpow hM0.le hMN0 (show 0 ≤ (3/2:ℝ)+η by linarith)
  have hn := Real.rpow_le_rpow hM0.le hMN0 (show 0 ≤ (1:ℝ)+η by linarith)
  have hf := Real.rpow_le_rpow hM0.le hMN0 (show 0 ≤ (3/4:ℝ)+η by linarith)
  have hceil : Nat.ceil (Real.sqrt (H*(M:ℝ))/G) ≤ Nat.ceil (Real.sqrt (H*(N:ℝ))/G) :=
    Nat.ceil_mono (div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hMN0 hH.le)) hG.le)
  have hh := atkinson_harmonic_mono hceil
  have hh0 : (0:ℝ) ≤ (harmonic (Nat.ceil (Real.sqrt (H*(M:ℝ))/G)):ℝ) := by
    simpa only [harmonic_zero,Rat.cast_zero] using atkinson_harmonic_mono
      (Nat.zero_le (Nat.ceil (Real.sqrt (H*(M:ℝ))/G)))
  have h1 := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg R : (0:ℝ) ≤ _)
  have h2 := mul_le_mul
    (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 120*(R:ℝ)*Real.sqrt H/G))
    hh hh0 (by positivity)
  have h3 := mul_le_mul_of_nonneg_left hf
    (by positivity : 0 ≤ 2000*(R:ℝ)^2*H^(-(1/4:ℝ))*Real.sqrt L)
  exact add_le_add (add_le_add h1 h2) h3

theorem atkinsonLocalizedGapBudget_le_power {H G η L : ℝ} (N R : ℕ)
    (hH : 0 < H) (hG : 0 < G) (hη : 0 ≤ η) :
    atkinsonLocalizedGapBudget η H G L N R ≤ atkinsonPowerGapBudget η H G L N R := by
  unfold atkinsonLocalizedGapBudget atkinsonPowerGapBudget
  have hs : (∑ j ∈ Finset.range (Nat.clog 2 N),
      (((2^j:ℕ):ℝ)^(1/2+η))*((R:ℝ)*atkinsonNearRowBound H G (2^j)+
        (R:ℝ)^2*(2000*Real.sqrt (((2^j:ℕ):ℝ)*L/Real.sqrt (H*((2^j:ℕ):ℝ)))))) ≤
      ∑ j ∈ Finset.range (Nat.clog 2 N), atkinsonPowerGapTerm η H G L N R := by
    apply Finset.sum_le_sum
    intro j hj
    rw [atkinson_localized_gap_term_eq hH (pow_pos (by norm_num) _)]
    exact atkinsonPowerGapTerm_mono_index R hH hG hη (pow_pos (by norm_num) _)
      (Nat.pow_lt_of_lt_clog (Finset.mem_range.mp hj)).le
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Nat.clog 2 N) : (0:ℝ) ≤ _)
  exact hm.trans_eq (by simp; ring)

theorem atkinsonPowerGapBudget_zero_card (η H G L : ℝ) (N : ℕ) :
    atkinsonPowerGapBudget η H G L N 0 = 0 := by
  simp [atkinsonPowerGapBudget,atkinsonPowerGapTerm]
end MathCollab.Density.Stronger.Atkinson
