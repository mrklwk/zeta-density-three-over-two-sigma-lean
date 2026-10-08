module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from ZetaNeumannSeries.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_SOURCE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaNeumannRemainder
public import MathCollab.Density.Stronger.Fourth.SquareDivisorSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonY0Term (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaAtkinsonY0Integrand T G L n x

def zetaAtkinsonTwoTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaAtkinsonTwoTermIntegrand T G L n x

def zetaNeumannRemainderTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaNeumannRemainderIntegrand T G L n x

theorem norm_divisorDirichletTerm_real (s : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (s : ℂ) n‖ = ‖divisorWeight n‖ * (n : ℝ) ^ (-s) := by
  by_cases hn : n = 0
  · simp [hn, divisorDirichletTerm, LSeries.term, divisorWeight]
  simp only [divisorDirichletTerm, LSeries.norm_term_eq, hn, ite_false, divisorWeight,
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem exists_norm_zetaNeumannRemainderTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
        ‖zetaNeumannRemainderTerm T G L n‖ ≤ C * G * ‖divisorDirichletTerm (5 / 4) n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_integral_zetaNeumannRemainder_le
  refine ⟨2 * Real.pi * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  by_cases hn : n = 0
  · simp [hn, zetaNeumannRemainderTerm, divisorWeight, divisorDirichletTerm, LSeries.term]
  have hpi : ‖(-(2 * Real.pi) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hd := norm_divisorDirichletTerm_real (5 / 4) n
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hd
  rw [zetaNeumannRemainderTerm, norm_mul, norm_mul, hpi, hd]
  calc
    _ ≤ ‖divisorWeight n‖ * (2 * Real.pi) * (C * G * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound T G L hT hG hGT hL hwidth n (Nat.pos_of_ne_zero hn))
        (by positivity)
    _ = _ := by ring

theorem summable_zetaNeumannRemainderTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (zetaNeumannRemainderTerm T G L) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_zetaNeumannRemainderTerm_le
  exact Summable.of_norm_bounded
    ((summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm.mul_left (C * G))
    (hbound T G L hT hG hGT hL hwidth)

theorem zetaAtkinsonTwoTerm_eq_sub {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (n : ℕ) :
    zetaAtkinsonTwoTerm T G L n =
      zetaAtkinsonY0Term T G L n - zetaNeumannRemainderTerm T G L n := by
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonTwoTerm, zetaAtkinsonY0Term, zetaNeumannRemainderTerm, divisorWeight]
  unfold zetaAtkinsonTwoTerm zetaAtkinsonY0Term zetaNeumannRemainderTerm
  simp_rw [zetaAtkinsonTwoTermIntegrand_eq_sub]
  rw [integral_sub
    (integrable_zetaAtkinsonY0Integrand hT hG hL hwidth (Nat.pos_of_ne_zero hn)).integrableOn
    (integrable_zetaNeumannRemainderIntegrand hT hG hL hwidth (Nat.pos_of_ne_zero hn)).integrableOn]
  ring

theorem exists_norm_tsum_zetaNeumannRemainderTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
        ‖∑' n : ℕ, zetaNeumannRemainderTerm T G L n‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaNeumannRemainderTerm_le
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (5 / 4) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs := summable_zetaNeumannRemainderTerm hT hG hGT hL hwidth
  have hd := (summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖zetaNeumannRemainderTerm T G L n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (C * G) * ‖divisorDirichletTerm (5 / 4) n‖ :=
      hs.norm.tsum_le_tsum (hbound T G L hT hG hGT hL hwidth) (hd.mul_left _)
    _ = C * G * S := tsum_mul_left
    _ ≤ _ := by nlinarith

end MathCollab.Density.Stronger.Atkinson
