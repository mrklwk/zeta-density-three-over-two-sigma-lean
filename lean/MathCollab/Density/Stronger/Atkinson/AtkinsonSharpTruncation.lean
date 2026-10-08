module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonBandSecondOrder
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLeadingFinite
public import MathCollab.Density.Stronger.Atkinson.NeumannRemainderSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Source-scale truncation of the complete actual leading series

The true ordinary-divisor Dirichlet series sums the inverse-index gain.
The cutoff is of size T(L/G)^2, not the previous coarse polynomial cutoff.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex
open MathCollab.Density.Stronger.Fourth

namespace MathCollab.Density.Stronger.Atkinson

theorem exists_norm_atkinsonLeadingTerm_band_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ n : ℕ, 36 * T * (L / G) ^ 2 ≤ (n : ℝ) →
      ‖atkinsonLeadingTerm T G L n‖ ≤ C * G ^ 2 * L * T ^ (-(3 / 4 : ℝ)) *
        ‖divisorDirichletTerm (5 / 4) n‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_atkinsonPowerPair_band_secondOrder_le (1 / 4) neumannLeadingPlus neumannLeadingMinus
  let q : ℝ := Real.sqrt Real.pi / Real.pi
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨2 * Real.pi * q * (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n hband
  by_cases hn : n = 0
  · simp [hn, atkinsonLeadingTerm, divisorWeight, divisorDirichletTerm, LSeries.term]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hT0 : 0 < T := by linarith
  have hnPow : (n : ℝ) ^ (-(1 / 4 : ℝ)) / n = (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    conv_lhs => rhs; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_sub hn0]
    norm_num
  have hTPow : T ^ (-(1 / 4 : ℝ)) / Real.sqrt T = T ^ (-(3 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hT0]
    norm_num
  have hpi : ‖(-(2 * Real.pi) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hqn : ‖(Real.sqrt Real.pi / Real.pi : ℂ)‖ = q := by
    simp [q, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hs : ‖(atkinsonBesselScale (1 / 4) n : ℂ)‖ = atkinsonBesselScale (1 / 4) n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (atkinsonBesselScale_nonneg _ _)]
  have hd := norm_divisorDirichletTerm_real (5 / 4) n
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hd
  rw [atkinsonLeadingTerm, atkinsonLeadingIntegral, norm_mul, norm_mul, norm_mul,
    norm_mul, hpi, hqn, hs, hd]
  calc
    _ ≤ ‖divisorWeight n‖ * (2 * Real.pi) *
        (q * atkinsonBesselScale (1 / 4) n *
          (C * G ^ 2 * T ^ (-(1 / 4 : ℝ)) * L / (Real.sqrt T * n))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left (hbound T G L hT0 hG hGT hL hwidth n hband)
      exact mul_nonneg hq.le (atkinsonBesselScale_nonneg _ _)
    _ = (2 * Real.pi * q * (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * C) * G ^ 2 * L *
        (T ^ (-(1 / 4 : ℝ)) / Real.sqrt T) *
          (‖divisorWeight n‖ * ((n : ℝ) ^ (-(1 / 4 : ℝ)) / n)) := by
      unfold atkinsonBesselScale
      norm_num only [show (-2 : ℝ) * (1 / 4) = -(1 / 2) by norm_num]
      ring
    _ = _ := by rw [hnPow, hTPow]

/-- The exact band majorant proves convergence after finitely many retained terms.
This native join avoids importing the unrelated coarse Fourier-tail chain. -/
theorem summable_atkinsonLeadingTerm_of_band {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 1 ≤ G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 1 ≤ L) (hwidth : 8 * L ≤ G) :
    Summable (atkinsonLeadingTerm T G L) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_atkinsonLeadingTerm_band_le
  let N : ℕ := atkinsonSourceCutoff T G L
  have hd := (summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm
  have hdn := (summable_nat_add_iff N).2 hd
  apply (summable_nat_add_iff N).1
  apply Summable.of_norm_bounded (hdn.mul_left (C * G ^ 2 * L * T ^ (-(3 / 4 : ℝ))))
  intro n
  apply hbound T G L hT hG hGT hL hwidth (n + N)
  exact (atkinsonSourceCutoff_lower T G L).trans (by exact_mod_cast Nat.le_add_left N n)

theorem exists_norm_atkinsonLeadingSum_sub_band_finite_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ N : ℕ, 36 * T * (L / G) ^ 2 ≤ (N : ℝ) →
      ‖atkinsonLeadingSum T G L - atkinsonLeadingFiniteSum T G L N‖ ≤
        C * G ^ 2 * L * T ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonLeadingTerm_band_le
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (5 / 4) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth N hN
  have hs := summable_atkinsonLeadingTerm_of_band hT hG hGT hL hwidth
  have hsn := (summable_nat_add_iff N).2 hs
  have hd := (summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm
  have hdn := (summable_nat_add_iff N).2 hd
  have he : atkinsonLeadingSum T G L - atkinsonLeadingFiniteSum T G L N =
      ∑' n : ℕ, atkinsonLeadingTerm T G L (n + N) := by
    have h := hs.sum_add_tsum_nat_add N
    unfold atkinsonLeadingSum atkinsonLeadingFiniteSum
    linear_combination -h
  have htail : (∑' n : ℕ, ‖divisorDirichletTerm (5 / 4) (n + N)‖) ≤ S := by
    have h := hd.sum_add_tsum_nat_add N
    have hpos : 0 ≤ ∑ n ∈ Finset.range N, ‖divisorDirichletTerm (5 / 4) n‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp [S]
    linarith
  let K : ℝ := C * G ^ 2 * L * T ^ (-(3 / 4 : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [he]
  calc
    _ ≤ ∑' n : ℕ, ‖atkinsonLeadingTerm T G L (n + N)‖ := norm_tsum_le_tsum_norm hsn.norm
    _ ≤ ∑' n : ℕ, K * ‖divisorDirichletTerm (5 / 4) (n + N)‖ := by
      apply hsn.norm.tsum_le_tsum _ (hdn.mul_left K)
      intro n
      apply hbound T G L hT hG hGT hL hwidth (n + N)
      exact hN.trans (by exact_mod_cast Nat.le_add_left N n)
    _ = K * ∑' n : ℕ, ‖divisorDirichletTerm (5 / 4) (n + N)‖ := tsum_mul_left
    _ ≤ K * S := mul_le_mul_of_nonneg_left htail hK
    _ ≤ _ := by dsimp [K]; nlinarith

theorem atkinsonBand_tail_scale_le {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 ≤ G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 0 ≤ L) (hLT : L ≤ T ^ (1 / 4 : ℝ)) :
    G ^ 2 * L * T ^ (-(3 / 4 : ℝ)) ≤ 2 * G := by
  have hT0 : 0 < T := by linarith
  have hs : G ≤ 2 * Real.sqrt T := by
    nlinarith [Real.sq_sqrt hT0.le, Real.sqrt_nonneg T]
  have hp : Real.sqrt T * T ^ (1 / 4 : ℝ) * T ^ (-(3 / 4 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    norm_num
  calc
    _ ≤ G * (2 * Real.sqrt T) * T ^ (1 / 4 : ℝ) * T ^ (-(3 / 4 : ℝ)) := by
      rw [pow_two]
      gcongr
    _ = 2 * G * (Real.sqrt T * T ^ (1 / 4 : ℝ) * T ^ (-(3 / 4 : ℝ))) := by ring
    _ = _ := by rw [hp, mul_one]

end MathCollab.Density.Stronger.Atkinson
