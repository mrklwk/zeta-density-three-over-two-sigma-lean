module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonBandAmplitude

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Summable second-order decay outside the source band

Both actual carriers have inverse-square frequency decay, with natural
source scales and no assumed tail estimate or endpoint condition.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonRootBand_derivative_bracket {T G L : ℝ}
    (hT : 0 < T) (hG : 1 ≤ G) (hL : 1 ≤ L) (hwidth : 8 * L ≤ G) :
    32 * (G / Real.sqrt T) + (atkinsonRootBandUpper T G L - atkinsonRootBandLower T G L) *
      (32 * (G / Real.sqrt T)) ^ 2 ≤ 4128 * L * (G / Real.sqrt T) := by
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hS : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hlen := atkinsonRootBand_length_le hT hG0 hL0 hwidth
  calc
    _ ≤ 32 * (G / Real.sqrt T) + (4 * Real.sqrt T * (L / G)) *
        (32 * (G / Real.sqrt T)) ^ 2 := by gcongr
    _ = (32 + 4096 * L) * (G / Real.sqrt T) := by field_simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith

theorem exists_norm_atkinsonPowerIntegral_band_secondOrder_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 6 * Real.sqrt T * (L / G) ≤ b →
      ‖atkinsonPowerIntegral T G L α b‖ ≤
        C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * b ^ 2) ∧
      ‖atkinsonPowerIntegral T G L α (-b)‖ ≤
        C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * b ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonSlopeQuotient_band α
  refine ⟨8256 * C / Real.pi ^ 2, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth hb
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hS : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hb0 : 0 < b := (by positivity : 0 < 6 * Real.sqrt T * (L / G)).trans_le hb
  have ha := atkinsonRootBandLower_pos hT G L
  have hab := atkinsonRootBand_order hT hG0 hL0.le
  have hfend := atkinsonPowerWeight_rootBand_endpoints hT hG0 hL0 α
  have hbracket := atkinsonRootBand_derivative_bracket hT hG hL hwidth
  have hp (u : ℝ)
      (hlo : ∀ y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L),
        b ≤ |atkinsonRootSlope T u y|)
      (hprimitive : ∀ x ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L),
        ‖∫ y in atkinsonRootBandLower T G L..x, atkinsonRootKernel T u y‖ ≤ 1 / (b * Real.pi)) :
      ‖atkinsonPowerIntegral T G L α u‖ ≤
        (8256 * C / Real.pi ^ 2) * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * b ^ 2) := by
    have hw := hbound T G L b u hT hG hGT hL hwidth hb hlo
    have h := hw.atkinsonRoot_secondOrder ha hab
      (fun y hy => abs_pos.mp (hb0.trans_le (hlo y hy))) hfend.1 hfend.2 hprimitive
    rw [atkinsonPowerIntegral_eq_root_band hT hG0 hL0 α u, norm_mul, norm_ofNat]
    calc
      _ ≤ 2 * ((1 / (b * Real.pi)) * (C * G * T ^ (-α) / b) *
          (32 * (G / Real.sqrt T) + (atkinsonRootBandUpper T G L - atkinsonRootBandLower T G L) *
            (32 * (G / Real.sqrt T)) ^ 2) / Real.pi) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ 2 * ((1 / (b * Real.pi)) * (C * G * T ^ (-α) / b) *
          (4128 * L * (G / Real.sqrt T)) / Real.pi) := by gcongr
      _ = _ := by field_simp; ring
  constructor
  · apply hp b
    · intro y hy
      exact (atkinsonRootSlope_outside_band hT hG0 hL0 hwidth hy hb).1.trans (le_abs_self _)
    · intro x hx
      exact (norm_atkinsonRootKernel_integral_outside_band hT hG0 hL0 hwidth hx hb).1
  · apply hp (-b)
    · intro y hy
      have h := (atkinsonRootSlope_outside_band hT hG0 hL0 hwidth hy hb).2
      exact (show b ≤ -atkinsonRootSlope T (-b) y by linarith).trans (neg_le_abs _)
    · intro x hx
      exact (norm_atkinsonRootKernel_integral_outside_band hT hG0 hL0 hwidth hx hb).2

theorem exists_norm_atkinsonPowerIntegral_index_band_secondOrder_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ n : ℕ, 36 * T * (L / G) ^ 2 ≤ (n : ℝ) →
      ‖atkinsonPowerIntegral T G L α (Real.sqrt n)‖ ≤
        C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * n) ∧
      ‖atkinsonPowerIntegral T G L α (-Real.sqrt n)‖ ≤
        C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * n) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonPowerIntegral_band_secondOrder_le α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  have hb : 6 * Real.sqrt T * (L / G) ≤ Real.sqrt (n : ℝ) := by
    have hs : (6 * Real.sqrt T * (L / G)) ^ 2 = 36 * T * (L / G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]
      ring
    have hn0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),
      show 0 ≤ 6 * Real.sqrt T * (L / G) by positivity]
  simpa only [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)] using
    hbound T G L (Real.sqrt n) hT hG hGT hL hwidth hb

theorem exists_norm_atkinsonPowerPair_band_secondOrder_le (α : ℝ) (cPlus cMinus : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ n : ℕ, 36 * T * (L / G) ^ 2 ≤ (n : ℝ) →
      ‖cPlus * atkinsonPowerIntegral T G L α (Real.sqrt n) +
        cMinus * atkinsonPowerIntegral T G L α (-Real.sqrt n)‖ ≤
        C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * n) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonPowerIntegral_index_band_secondOrder_le α
  refine ⟨(1 + ‖cPlus‖ + ‖cMinus‖) * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  have h := hbound T G L hT hG hGT hL hwidth n hn
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have hp := mul_le_mul_of_nonneg_left h.1 (norm_nonneg cPlus)
  have hm := mul_le_mul_of_nonneg_left h.2 (norm_nonneg cMinus)
  have hpos : 0 ≤ C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * n) := by positivity
  calc
    _ ≤ (‖cPlus‖ + ‖cMinus‖) * (C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * n)) := by nlinarith
    _ ≤ (1 + ‖cPlus‖ + ‖cMinus‖) * (C * G ^ 2 * T ^ (-α) * L / (Real.sqrt T * n)) := by nlinarith
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
