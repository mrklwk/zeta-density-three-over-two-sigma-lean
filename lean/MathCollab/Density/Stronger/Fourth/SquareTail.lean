module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/FOURTH_MOMENT_MANIFEST.json.
Mathlib and narrow DigammaSeries dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.SquareTruncation
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open MathCollab.Density.Stronger
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth


theorem tsum_nat_rpow_tail_le {p : ℝ} (hp : p < -1) {N : ℕ} (hN : 0 < N) :
    (∑' j : ℕ, ((j+N+1:ℕ):ℝ)^p) ≤ (N:ℝ)^(p+1)/(-p-1) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hi := integrableOn_Ioi_rpow_of_lt hp hN0
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro k
  have hanti : AntitoneOn (fun x : ℝ => x^p) (Icc (N:ℝ) ((N:ℝ)+k)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : p ≤ 0)).mono
      (fun _ hx => hN0.trans_le hx.1)
  calc
    (∑ j ∈ Finset.range k, ((j+N+1:ℕ):ℝ)^p)
        ≤ ∫ x : ℝ in (N:ℝ)..(N:ℝ)+k, x^p := by
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
        hanti.sum_le_integral
    _ ≤ ∫ x : ℝ in Ioi (N:ℝ), x^p := by
      rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg k))]
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (hN0.le.trans hx.le) _
      · exact Eventually.of_forall (fun _ hx => hx.1)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt hp hN0,
        show -p-1 = -(p+1) by ring,div_neg,neg_div]

theorem fourth_divisorWeight_le_rpow (b : ℝ) (n : ℕ) :
    (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+b)) ≤ (n:ℝ)^(1/2-b) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.divisors_zero,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ (n:ℝ)*(n:ℝ)^(-(1/2+b)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n)
        (Real.rpow_nonneg hn0.le _)
    _ = (n:ℝ)^(1+(-(1/2+b))) := by rw [Real.rpow_add hn0,Real.rpow_one]
    _ = _ := by congr 1; ring

theorem tsum_fourth_divisorWeight_tail_le {b : ℝ} (hb : 3/2 < b)
    {N : ℕ} (hN : 0 < N) :
    (∑' n : {n : ℕ // n ∉ Finset.range (N+1)},
      ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))) ≤
      (N:ℝ)^(3/2-b)/(b-3/2) := by
  have hp : 1/2-b < (-1:ℝ) := by linarith
  have hs := (Real.summable_nat_rpow.mpr hp).subtype
    (fun n => n ∉ Finset.range (N+1))
  calc
    _ ≤ ∑' n : {n : ℕ // n ∉ Finset.range (N+1)}, ((n:ℕ):ℝ)^(1/2-b) :=
      Summable.tsum_le_tsum (fun n => fourth_divisorWeight_le_rpow b n)
        ((summable_fourth_divisorWeight hb).subtype _) hs
    _ = ∑' j : ℕ, ((j+N+1:ℕ):ℝ)^(1/2-b) := by
      simpa only [coe_notMemRangeEquiv_symm,Nat.add_assoc] using
        ((notMemRangeEquiv (N+1)).symm.tsum_eq
          (fun n : {n : ℕ // n ∉ Finset.range (N+1)} =>
            ((n:ℕ):ℝ)^(1/2-b))).symm
    _ ≤ _ := by
      have h := tsum_nat_rpow_tail_le hp hN
      have hnum : (1/2-b)+1 = 3/2-b := by ring
      have hden : -(1/2-b)-1 = b-3/2 := by ring
      simpa only [hnum,hden] using h

theorem exists_norm_zetaFourthTail_cutoff_le {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ N : ℕ, 0 < N →
      ‖zetaFourthTail t b (Finset.range (N+1))‖ ≤
        K*t^b*(N:ℝ)^(3/2-b) := by
  obtain ⟨A,hA,hbound⟩ := exists_norm_zetaFourthTail_le hb
  refine ⟨A/(b-3/2),div_pos hA (by linarith),?_⟩
  intro t ht hbt N hN
  calc
    _ ≤ A*t^b*(∑' n : {n : ℕ // n ∉ Finset.range (N+1)},
        ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))) :=
      hbound t ht hbt _
    _ ≤ A*t^b*((N:ℝ)^(3/2-b)/(b-3/2)) :=
      mul_le_mul_of_nonneg_left (tsum_fourth_divisorWeight_tail_le hb hN)
        (by positivity)
    _ = _ := by ring




theorem fourth_tail_scale_le {δ b H t x : ℝ}
    (hH : 1 ≤ H) (ht : 0 ≤ t) (htH : t ≤ 2*H)
    (hb : 3/2 < b) (hbudget : b+(1+δ)*(3/2-b) ≤ 0)
    (hx : H^(1+δ) ≤ x) :
    t^b*x^(3/2-b) ≤ 2^b := by
  have hH0 : 0 < H := by linarith
  have hx0 : 0 < H^(1+δ) := Real.rpow_pos_of_pos hH0 _
  have hbp : 0 ≤ b := by linarith
  have hbn : 3/2-b ≤ 0 := by linarith
  calc
    _ ≤ (2*H)^b*(H^(1+δ))^(3/2-b) :=
      mul_le_mul (Real.rpow_le_rpow ht htH hbp)
        (Real.rpow_le_rpow_of_nonpos hx0 hx hbn)
        (Real.rpow_nonneg (hx0.le.trans hx) _) (by positivity)
    _ = 2^b*H^(b+(1+δ)*(3/2-b)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH0.le,
        ← Real.rpow_mul hH0.le,mul_assoc,← Real.rpow_add hH0]
    _ ≤ 2^b*1 :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hH hbudget)
        (by positivity)
    _ = _ := mul_one _

theorem exists_norm_fourthRightPiece_sub_cutoff_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∃ H₀ : ℝ, 4 ≤ H₀ ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ t : ℝ, H ≤ t → t ≤ 2*H →
      ∀ N : ℕ, H^(1+δ) ≤ (N:ℝ) → ∀ a : ℝ, 0 < a →
      ‖zetaFourthRightPiece t-zetaFourthPrefix t a (Finset.range (N+1))‖ ≤ K := by
  let b : ℝ := 2+2/δ
  have hb : 3/2 < b := by
    have h := div_pos (by norm_num : (0:ℝ)<2) hδ
    dsimp [b]
    linarith
  have hbudget : b+(1+δ)*(3/2-b) ≤ 0 := by
    have heq : b+(1+δ)*(3/2-b) = -(1+δ)/2 := by
      dsimp [b]
      field_simp [hδ.ne']
      ring
    rw [heq]
    linarith
  obtain ⟨A,hA,hbound⟩ := exists_norm_zetaFourthTail_cutoff_le hb
  refine ⟨A*2^b,by positivity,max 4 (4*b),le_max_left _ _,?_⟩
  intro H hH t ht htH N hN a ha
  have hH4 : 4 ≤ H := (le_max_left _ _).trans hH
  have hHt : 4*b ≤ H := (le_max_right _ _).trans hH
  have ht0 : 0 ≤ t := by linarith
  have hNpos : 0 < N := by
    have hNreal : (0:ℝ) < N :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith : 0 < H) _) hN
    exact_mod_cast hNreal
  rw [zetaFourthRightPiece_eq_prefix_add_tail ht0 ha (by linarith : 0 < b)
    (Finset.range (N+1)),add_sub_cancel_left]
  calc
    _ ≤ A*t^b*(N:ℝ)^(3/2-b) :=
      hbound t (hH4.trans ht) (hHt.trans ht) N hNpos
    _ = A*(t^b*(N:ℝ)^(3/2-b)) := by ring
    _ ≤ A*2^b :=
      mul_le_mul_of_nonneg_left
        (fourth_tail_scale_le (by linarith) ht0 htH hb hbudget hN) hA.le



end MathCollab.Density.Stronger.Fourth
