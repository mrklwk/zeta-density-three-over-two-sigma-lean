module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/FOURTH_MOMENT_MANIFEST.json.
Mathlib and narrow DigammaSeries dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.SquareLineShift
public import Mathlib.Analysis.PSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open MathCollab.Density.Stronger
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth


theorem integral_norm_zetaFourthTerm_vertical (t c : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖) =
      ((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ∫ u : ℝ, ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ := by
  simp_rw [norm_zetaFourthTerm_vertical]
  exact integral_const_mul _ _

theorem exists_norm_zetaFourthContribution_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ n : ℕ,
      ‖zetaFourthContribution t c n‖ ≤
        K*t^c*((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) := by
  obtain ⟨A,hA,hbound⟩ := exists_integral_norm_zetaFourthKernel_le hc
  let B : ℝ := ‖(1/(2*Real.pi):ℂ)‖
  have hB : 0 < B := by
    apply norm_pos_iff.mpr
    exact one_div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  let K : ℝ := B*A*Real.sqrt (Real.pi/98)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro t ht hct n
  calc
    ‖zetaFourthContribution t c n‖
        ≤ B*(∫ u : ℝ, ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖) := by
      rw [zetaFourthContribution,norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hB.le
    _ = B*(((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ∫ u : ℝ, ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖) := by
      rw [integral_norm_zetaFourthTerm_vertical]
    _ ≤ B*(((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        (A*t^c*Real.sqrt (Real.pi/98))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbound t ht hct) (by positivity)) hB.le
    _ = _ := by dsimp [K]; ring

theorem summable_fourth_divisorWeight {c : ℝ} (hc : 3/2 < c) :
    Summable (fun n : ℕ => (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) := by
  have hp : Summable (fun n : ℕ => (n:ℝ)^(1/2-c)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) ?_ hp
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.divisors_zero,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ (n:ℝ)*(n:ℝ)^(-(1/2+c)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n)
        (Real.rpow_nonneg hn0.le _)
    _ = (n:ℝ)^(1+(-(1/2+c))) := by
      rw [Real.rpow_add hn0,Real.rpow_one]
    _ = _ := by congr 1; ring




def zetaFourthPrefix (t c : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, zetaFourthContribution t c n

def zetaFourthTail (t c : ℝ) (S : Finset ℕ) : ℂ :=
  ∑' n : {n : ℕ // n ∉ S}, zetaFourthContribution t c n

theorem zetaFourthPrefix_eq_integral {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (S : Finset ℕ) :
    zetaFourthPrefix t c S = (1/(2*Real.pi):ℂ) *
      ∫ u : ℝ, (∑ n ∈ S,
        divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n) *
          zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I) := by
  unfold zetaFourthPrefix zetaFourthContribution
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum S (fun n _ => integrable_zetaFourthTerm_vertical ht hc n)]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [zetaFourthTerm,Finset.sum_mul]

theorem zetaFourthPrefix_line_eq {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaFourthPrefix t a S = zetaFourthPrefix t b S := by
  apply Finset.sum_congr rfl
  intro n _
  exact zetaFourthContribution_line_eq ha hb ht n

theorem zetaFourthRightPiece_eq_prefix_add_tail {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaFourthRightPiece t = zetaFourthPrefix t a S + zetaFourthTail t b S := by
  rw [zetaFourthPrefix_line_eq ht ha hb S,zetaFourthPrefix,zetaFourthTail,
    (hasSum_zetaFourthContribution ht hb).summable.sum_add_tsum_subtype_compl S,
    (hasSum_zetaFourthContribution ht hb).tsum_eq]

theorem summable_norm_zetaFourthTail {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (S : Finset ℕ) :
    Summable (fun n : {n : ℕ // n ∉ S} => ‖zetaFourthContribution t c n‖) :=
  ((hasSum_zetaFourthContribution ht hc).summable.subtype _).norm

theorem exists_norm_zetaFourthTail_le {c : ℝ} (hc : 3/2 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ S : Finset ℕ,
      ‖zetaFourthTail t c S‖ ≤ K*t^c*
        ∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+c)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthContribution_le hc0
  refine ⟨K,hK,?_⟩
  intro t ht hct S
  have ht0 : 0 ≤ t := by linarith
  have hs := (summable_fourth_divisorWeight hc).subtype (fun n => n ∉ S)
  calc
    ‖zetaFourthTail t c S‖ ≤
        ∑' n : {n : ℕ // n ∉ S}, ‖zetaFourthContribution t c n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_zetaFourthTail ht0 hc0 S)
    _ ≤ ∑' n : {n : ℕ // n ∉ S},
        K*t^c*(((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+c))) :=
      Summable.tsum_le_tsum (fun n => hbound t ht hct n)
        (summable_norm_zetaFourthTail ht0 hc0 S) (hs.mul_left (K*t^c))
    _ = _ := tsum_mul_left

theorem exists_norm_fourthRightPiece_sub_prefix_le {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ a : ℝ, 0 < a → ∀ S : Finset ℕ,
      ‖zetaFourthRightPiece t - zetaFourthPrefix t a S‖ ≤ K*t^b*
        ∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b)) := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthTail_le hb
  refine ⟨K,hK,?_⟩
  intro t ht hbt a ha S
  rw [zetaFourthRightPiece_eq_prefix_add_tail (by linarith : 0 ≤ t)
    ha (by linarith : 0 < b) S,add_sub_cancel_left]
  exact hbound t ht hbt S

theorem zeta_fourth_le_prefix_add_tail {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaMomentCriticalNorm t^4 ≤
      8*‖zetaFourthPrefix t a S‖^2 + 8*‖zetaFourthTail t b S‖^2 := by
  have hz := zeta_fourth_le_four_mul_rightPiece_sq t
  rw [zetaFourthRightPiece_eq_prefix_add_tail ht ha hb S] at hz
  have hnorm := norm_add_le (zetaFourthPrefix t a S) (zetaFourthTail t b S)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_nonneg (‖zetaFourthPrefix t a S‖-‖zetaFourthTail t b S‖)]

theorem exists_zeta_fourth_le_prefix_add_weightTail {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ a : ℝ, 0 < a → ∀ S : Finset ℕ,
      zetaMomentCriticalNorm t^4 ≤ 8*‖zetaFourthPrefix t a S‖^2 +
        8*(K*t^b*(∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))))^2 := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthTail_le hb
  refine ⟨K,hK,?_⟩
  intro t ht hbt a ha S
  have h := zeta_fourth_le_prefix_add_tail (by linarith : 0 ≤ t)
    ha (by linarith : 0 < b) S
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hbound t ht hbt S) 2
  linarith



end MathCollab.Density.Stronger.Fourth
