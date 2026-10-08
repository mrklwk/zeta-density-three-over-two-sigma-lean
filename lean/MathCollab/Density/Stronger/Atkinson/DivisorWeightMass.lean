module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightVariation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem min_one_le_rpow {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min 1 a ≤ a ^ θ := by
  by_cases ha1 : a ≤ 1
  · rw [min_eq_right ha1]
    exact Real.self_le_rpow_of_le_one ha ha1 hθ1
  · rw [min_eq_left (le_of_not_ge ha1)]
    exact Real.one_le_rpow (le_of_not_ge ha1) hθ

theorem norm_divisorCritical_mul_ratio_rpow {A : ℝ} (hA : 0 < A)
    (t θ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * (A / (n : ℝ)) ^ θ =
      A ^ θ * ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [divisorDirichletTerm, LSeries.norm_term_eq, hn.ne', ite_false,
    afeCriticalPoint, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  norm_num only [div_ofNat_re, one_re]
  rw [Real.div_rpow hA.le hnR.le, Real.rpow_add hnR]
  ring

theorem norm_divisorCritical_mul_min_le {A θ : ℝ} (hA : 0 < A)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 (A / (n : ℝ)) ≤
      A ^ θ * ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖ := by
  by_cases hn : n = 0
  · simp [hn, divisorDirichletTerm, LSeries.term]
  calc
    _ ≤ ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * (A / (n : ℝ)) ^ θ :=
      mul_le_mul_of_nonneg_left (min_one_le_rpow (by positivity) hθ hθ1) (norm_nonneg _)
    _ = _ := norm_divisorCritical_mul_ratio_rpow hA t θ (Nat.pos_of_ne_zero hn)

theorem summable_divisorCritical_min {A θ : ℝ} (hA : 0 < A)
    (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    Summable (fun n : ℕ => ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 (A / (n : ℝ))) := by
  have hs := (summable_divisorDirichletTerm (s := ((1 / 2 + θ : ℝ) : ℂ))
    (by simp only [ofReal_re]; linarith)).norm
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (norm_divisorCritical_mul_min_le hA (by linarith) hθ1 t) (hs.mul_left (A ^ θ))

theorem tsum_divisorCritical_min_le {A θ : ℝ} (hA : 0 < A)
    (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    (∑' n : ℕ, ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 (A / (n : ℝ))) ≤
      A ^ θ * ∑' n : ℕ, ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖ := by
  have hs := (summable_divisorDirichletTerm (s := ((1 / 2 + θ : ℝ) : ℂ))
    (by simp only [ofReal_re]; linarith)).norm
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (norm_divisorCritical_mul_min_le hA (by linarith) hθ1 t)
    (summable_divisorCritical_min hA hθ hθ1 t) (hs.mul_left (A ^ θ))

theorem summable_norm_source_divisor_weight {T : ℝ} (hT : 0 < T) (t : ℝ) :
    Summable (fun n : ℕ => ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
      ‖zetaDivisorWeight (zetaDivisorWeightArgument T n)‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_source_zetaDivisorWeight_min_le
  have hs := (summable_divisorCritical_min (A := T / (2 * Real.pi)) (θ := 3 / 4)
    (by positivity) (by norm_num) (by norm_num) t).mul_left C
  apply Summable.of_nonneg_of_le (fun n => by positivity) ?_ hs
  intro n
  by_cases hn : n = 0
  · simp [hn, divisorDirichletTerm, LSeries.term]
  have h := mul_le_mul_of_nonneg_left (hbound T hT n (Nat.pos_of_ne_zero hn))
    (norm_nonneg (divisorDirichletTerm (afeCriticalPoint t) n))
  simpa only [div_div, mul_assoc, mul_comm, mul_left_comm] using h

/-- A single constant for all heights and all oscillatory phases of the
critical-line divisor coefficient. The loss is arbitrarily small. -/
theorem exists_tsum_norm_source_divisor_weight_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ t : ℝ,
      (∑' n : ℕ, ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
        ‖zetaDivisorWeight (zetaDivisorWeightArgument T n)‖) ≤ C * T ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_source_zetaDivisorWeight_min_le
  let θ : ℝ := 1 / 2 + min (ε / 2) (1 / 4)
  have hθ : 1 / 2 < θ := by
    have hm : 0 < min (ε / 2) (1 / 4 : ℝ) := lt_min (by positivity) (by norm_num)
    dsimp [θ]
    linarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith [min_le_right (ε / 2) (1 / 4)]
  have hθε : θ ≤ 1 / 2 + ε := by dsimp [θ]; linarith [min_le_left (ε / 2) (1 / 4)]
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨1 + C * S, by positivity, ?_⟩
  intro T hT t
  have hT0 : 0 < T := by linarith
  have hpoint (n : ℕ) : ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
      ‖zetaDivisorWeight (zetaDivisorWeightArgument T n)‖ ≤
      C * (‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 ((T / (2 * Real.pi)) / (n : ℝ))) := by
    by_cases hn : n = 0
    · simp [hn, divisorDirichletTerm, LSeries.term]
    have h := mul_le_mul_of_nonneg_left (hbound T hT0 n (Nat.pos_of_ne_zero hn))
      (norm_nonneg (divisorDirichletTerm (afeCriticalPoint t) n))
    simpa only [div_div, mul_assoc, mul_comm, mul_left_comm] using h
  have hsum := Summable.tsum_le_tsum hpoint (summable_norm_source_divisor_weight hT0 t)
    ((summable_divisorCritical_min (by positivity) hθ hθ1 t).mul_left C)
  rw [tsum_mul_left] at hsum
  apply hsum.trans
  have hm := tsum_divisorCritical_min_le (A := T / (2 * Real.pi)) (by positivity) hθ hθ1 t
  have hpow : (T / (2 * Real.pi)) ^ θ ≤ T ^ (1 / 2 + ε) := by
    apply (Real.rpow_le_rpow (by positivity) (show T / (2 * Real.pi) ≤ T by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Real.pi_gt_three]) (by linarith : 0 ≤ θ)).trans
    exact Real.rpow_le_rpow_of_exponent_le hT hθε
  calc
    _ ≤ C * ((T / (2 * Real.pi)) ^ θ * S) := mul_le_mul_of_nonneg_left hm hC.le
    _ ≤ C * (T ^ (1 / 2 + ε) * S) := by gcongr
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hT0.le (1 / 2 + ε)]

/-- The comparison mass itself has the same square-root scale. It can
therefore control weight differences without needing any lower bound on
the complex weight, which can have cancellation. -/
theorem exists_tsum_divisorCritical_min_height_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ t : ℝ,
      (∑' n : ℕ, ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
        min 1 (T / (2 * Real.pi * (n : ℝ)))) ≤ C * T ^ (1 / 2 + ε) := by
  let θ : ℝ := 1 / 2 + min (ε / 2) (1 / 4)
  have hθ : 1 / 2 < θ := by
    have hm : 0 < min (ε / 2) (1 / 4 : ℝ) := lt_min (by positivity) (by norm_num)
    dsimp [θ]
    linarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith [min_le_right (ε / 2) (1 / 4)]
  have hθε : θ ≤ 1 / 2 + ε := by dsimp [θ]; linarith [min_le_left (ε / 2) (1 / 4)]
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨1 + S, by positivity, ?_⟩
  intro T hT t
  have hT0 : 0 < T := by linarith
  have hm := tsum_divisorCritical_min_le (A := T / (2 * Real.pi)) (by positivity) hθ hθ1 t
  simp only [div_div] at hm
  have hpow : (T / (2 * Real.pi)) ^ θ ≤ T ^ (1 / 2 + ε) := by
    apply (Real.rpow_le_rpow (by positivity) (show T / (2 * Real.pi) ≤ T by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Real.pi_gt_three]) (by linarith : 0 ≤ θ)).trans
    exact Real.rpow_le_rpow_of_exponent_le hT hθε
  apply hm.trans
  calc
    _ ≤ T ^ (1 / 2 + ε) * S := mul_le_mul_of_nonneg_right hpow hS
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hT0.le (1 / 2 + ε)]

end MathCollab.Density.Stronger.Atkinson
