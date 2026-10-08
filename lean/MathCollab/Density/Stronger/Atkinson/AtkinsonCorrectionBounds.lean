module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction; see third_party/twelfth/ATKINSON_CORRECTION_SERIES_MANIFEST.json.
Mathlib and the nonstationary foundations retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFrequencyTail
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerPairBound
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLeadingFinite
public import MathCollab.Density.Stronger.Atkinson.NeumannRemainderSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonCorrectionIntegral (T G L : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt Real.pi / Real.pi : ℂ) * ((atkinsonBesselScale (3 / 4) n : ℂ) / 8) *
    (neumannCorrectionPlus * atkinsonPowerIntegral T G L (3 / 4) (Real.sqrt n) +
     neumannCorrectionMinus * atkinsonPowerIntegral T G L (3 / 4) (-Real.sqrt n))

def atkinsonCorrectionTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * atkinsonCorrectionIntegral T G L n

theorem exists_norm_atkinsonPowerPair_far_le (α : ℝ) (c d : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → 8 * Real.sqrt T ≤ b →
      ‖c * atkinsonPowerIntegral T G L α b + d * atkinsonPowerIntegral T G L α (-b)‖ ≤
        C * G * T ^ (-α) / b := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonPowerIntegral_far_le α
  refine ⟨(1 + ‖c‖ + ‖d‖) * C, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth hb
  have hb0 : 0 < b := (by positivity : 0 < 8 * Real.sqrt T).trans_le hb
  have h := hbound T G L b hT hG hGT hL hwidth hb
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * (C * G * T ^ (-α) / b) + ‖d‖ * (C * G * T ^ (-α) / b) :=
      add_le_add (mul_le_mul_of_nonneg_left h.1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h.2 (norm_nonneg _))
    _ = (‖c‖ + ‖d‖) * (C * G * T ^ (-α) / b) := by ring
    _ ≤ (1 + ‖c‖ + ‖d‖) * (C * G * T ^ (-α) / b) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = _ := by ring

theorem atkinson_correction_height_absorb {T : ℝ} (hT : 1 ≤ T) :
    T ^ (-(3 / 4 : ℝ)) * Real.sqrt T ≤ 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith : 0 < T)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)

theorem exists_norm_atkinsonCorrectionPair_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ, 0 < n →
      ‖neumannCorrectionPlus * atkinsonPowerIntegral T G L (3 / 4) (Real.sqrt n) +
        neumannCorrectionMinus * atkinsonPowerIntegral T G L (3 / 4) (-Real.sqrt n)‖ ≤
          C * G / Real.sqrt n := by
  obtain ⟨C, hC, hnear⟩ :=
    exists_norm_atkinsonPowerPair_le (3 / 4) neumannCorrectionPlus neumannCorrectionMinus
  obtain ⟨D, hD, hfar⟩ :=
    exists_norm_atkinsonPowerPair_far_le (3 / 4) neumannCorrectionPlus neumannCorrectionMinus
  refine ⟨8 * C + D, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  by_cases hb : 8 * Real.sqrt T ≤ Real.sqrt (n : ℝ)
  · apply (hfar T G L (Real.sqrt n) hT0 hG hGT hL hwidth hb).trans
    apply div_le_div_of_nonneg_right _ hsn.le
    calc
      _ ≤ D * G := by
        have hp := Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num : -(3 / 4 : ℝ) ≤ 0)
        nlinarith [mul_nonneg hD.le hG.le]
      _ ≤ _ := by nlinarith
  · apply (hnear T G L (Real.sqrt n) hT0 hG hGT hL hwidth).trans
    apply (le_div_iff₀ hsn).2
    calc
      _ ≤ (C * G * T ^ (-(3 / 4 : ℝ))) * (8 * Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (le_of_not_ge hb) (by positivity)
      _ = (8 * C * G) * (T ^ (-(3 / 4 : ℝ)) * Real.sqrt T) := by ring
      _ ≤ 8 * C * G := by
        have h := mul_le_mul_of_nonneg_left (atkinson_correction_height_absorb hT)
          (show 0 ≤ 8 * C * G by positivity)
        simpa only [mul_one] using h
      _ ≤ _ := by nlinarith

theorem exists_norm_atkinsonCorrectionTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
        ‖atkinsonCorrectionTerm T G L n‖ ≤ C * G * ‖divisorDirichletTerm (5 / 4) n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonCorrectionPair_le
  let q : ℝ := Real.sqrt Real.pi / Real.pi
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨2 * Real.pi * q * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) / 8 * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  by_cases hn : n = 0
  · simp [hn, atkinsonCorrectionTerm, divisorWeight, divisorDirichletTerm, LSeries.term]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : (n : ℝ) ^ (-(3 / 4 : ℝ)) / Real.sqrt n =
      (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn0]
    norm_num
  have hpi : ‖(-(2 * Real.pi) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hqn : ‖(Real.sqrt Real.pi / Real.pi : ℂ)‖ = q := by
    simp [q, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hs : ‖(atkinsonBesselScale (3 / 4) n : ℂ)‖ = atkinsonBesselScale (3 / 4) n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (atkinsonBesselScale_nonneg _ _)]
  have hd := norm_divisorDirichletTerm_real (5 / 4) n
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hd
  rw [atkinsonCorrectionTerm, atkinsonCorrectionIntegral, norm_mul, norm_mul, norm_mul,
    norm_mul, hpi, hqn, norm_div, norm_ofNat, hs, hd]
  calc
    _ ≤ ‖divisorWeight n‖ * (2 * Real.pi) *
        (q * (atkinsonBesselScale (3 / 4) n / 8) * (C * G / Real.sqrt n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left
        (hbound T G L hT hG hGT hL hwidth n (Nat.pos_of_ne_zero hn))
      exact mul_nonneg hq.le (div_nonneg (atkinsonBesselScale_nonneg _ _) (by norm_num))
    _ = (2 * Real.pi * q * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) / 8 * C) * G *
        (‖divisorWeight n‖ * ((n : ℝ) ^ (-(3 / 4 : ℝ)) / Real.sqrt n)) := by
      unfold atkinsonBesselScale
      norm_num only [show (-2 : ℝ) * (3 / 4) = -(3 / 2) by norm_num]
      ring
    _ = _ := by rw [hpow]

end MathCollab.Density.Stronger.Atkinson
