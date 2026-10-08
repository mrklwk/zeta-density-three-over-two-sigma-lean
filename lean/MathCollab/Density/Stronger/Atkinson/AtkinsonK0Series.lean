module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonK0Integral
public import MathCollab.Density.Stronger.Fourth.SquareDivisorSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_divisorDirichletTerm_two (n : ℕ) :
    ‖divisorDirichletTerm 2 n‖ = ‖divisorWeight n‖ / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, divisorDirichletTerm, LSeries.term, divisorWeight]
  · simp only [divisorDirichletTerm, LSeries.norm_term_eq, hn, ite_false, divisorWeight]
    norm_num [Real.rpow_two]

theorem exists_norm_zetaAtkinsonBesselPlusTerm_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
      ‖zetaAtkinsonBesselPlusTerm T G L n‖ ≤
        (C * G * T / T ^ k) * ‖divisorDirichletTerm 2 n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_integral_zetaAtkinsonK0_le k
  refine ⟨4 * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonBesselPlusTerm, divisorWeight, divisorDirichletTerm, LSeries.term]
  have hnpos := Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hnk : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ k := pow_le_pow_right₀ hn1 hk
  have hsmall : C * G * T / (T ^ k * (n : ℝ) ^ k) ≤
      C * G * T / (T ^ k * (n : ℝ) ^ 2) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hnk (by positivity))
  unfold zetaAtkinsonBesselPlusTerm
  rw [norm_mul, norm_mul, norm_divisorDirichletTerm_two]
  norm_num only [norm_ofNat]
  calc
    _ ≤ ‖divisorWeight n‖ * 4 * (C * G * T / (T ^ k * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left ((hbound T G L hT hG hGT hL hwidth n hnpos).trans hsmall) (by positivity)
    _ = _ := by ring

theorem summable_zetaAtkinsonBesselPlusTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 0 < L) (hwidth : 8 * L ≤ G) : Summable (zetaAtkinsonBesselPlusTerm T G L) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselPlusTerm_le (k := 2) le_rfl
  exact Summable.of_norm_bounded
    (((summable_divisorDirichletTerm (s := (2 : ℂ)) (by norm_num)).norm).mul_left (C * G * T / T ^ 2))
    (hbound T G L hT hG hGT hL hwidth)

theorem hasSum_zetaAtkinsonBesselPlusTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    HasSum (zetaAtkinsonBesselPlusTerm T G L) (zetaAtkinsonBesselPlus T G L) :=
  (summable_zetaAtkinsonBesselPlusTerm hT hG hGT hL hwidth).hasSum

theorem exists_norm_zetaAtkinsonBesselPlus_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ‖zetaAtkinsonBesselPlus T G L‖ ≤ C * G * T / T ^ k := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselPlusTerm_le hk
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm 2 n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs := summable_zetaAtkinsonBesselPlusTerm hT hG hGT hL hwidth
  have hd := (summable_divisorDirichletTerm (s := (2 : ℂ)) (by norm_num)).norm
  have hnorm := norm_tsum_le_tsum_norm hs.norm
  change ‖∑' n : ℕ, zetaAtkinsonBesselPlusTerm T G L n‖ ≤ _
  calc
    _ ≤ ∑' n : ℕ, ‖zetaAtkinsonBesselPlusTerm T G L n‖ := hnorm
    _ ≤ ∑' n : ℕ, (C * G * T / T ^ k) * ‖divisorDirichletTerm 2 n‖ :=
      hs.norm.tsum_le_tsum (hbound T G L hT hG hGT hL hwidth) (hd.mul_left _)
    _ = (C * G * T / T ^ k) * S := tsum_mul_left
    _ ≤ _ := by
      have hpos : 0 ≤ C * G * T / T ^ k := by positivity
      have h := mul_le_mul_of_nonneg_left (show S ≤ 1 + S by linarith) hpos
      convert h using 1
      ring


end MathCollab.Density.Stronger.Atkinson
