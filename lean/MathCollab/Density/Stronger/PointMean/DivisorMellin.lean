module
-- Reversible module-visibility port of the audited development.
/-
Selected actual divisor Gamma-Mellin proofs from Scott McColm,
PointMeanDivisorMellin.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_SHIFT_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local GammaMellin infrastructure retains its Apache-2.0 attribution.
No upstream project module or moment premise is imported.
-/
public import MathCollab.Density.GammaMellin
public import MathCollab.Density.Stronger.Fourth.SquareSource

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter ArithmeticFunction
open MathCollab.Density.Stronger.Fourth
open scoped BigOperators Topology LSeries.notation
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

private theorem continuous_Gamma_two_vertical :
    Continuous (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
  intro n h
  have hr := congrArg Complex.re h
  simp at hr
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

private theorem integrable_Gamma_two_vertical :
    Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) := by
  exact GammaMellin.verticalIntegrable_Gamma (by norm_num : (0 : ℝ) < 2)

private theorem inverseMellin_exp_neg {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ t : ℝ, (x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I)) *
        Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) = (Real.exp (-x) : ℂ) := by
  simpa only [mul_comm, Complex.ofReal_ofNat] using
    (GammaMellin.exp_neg_eq_gamma_vertical_integral
      (sigma := 2) (by norm_num) hx).symm

noncomputable def heathBrownSmoothedDivisorTerm
    (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (n.divisors.card : ℂ) * (n : ℂ) ^ (-s) * Real.exp (-(n : ℝ))

noncomputable def heathBrownSmoothedDivisorSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, heathBrownSmoothedDivisorTerm s n

noncomputable def heathBrownDivisorMellinSeriesTerm
    (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  if n = 0 then 0 else
    let w : ℂ := (2 : ℂ) + (t : ℂ) * I
    (n.divisors.card : ℂ) * (n : ℂ) ^ (-s) *
      ((n : ℂ) ^ (-w) * Complex.Gamma w)

noncomputable def heathBrownDivisorMellinIntegrand
    (s : ℂ) (t : ℝ) : ℂ :=
  let w : ℂ := (2 : ℂ) + (t : ℂ) * I
  Complex.Gamma w * riemannZeta (s + w) ^ 2

theorem continuous_heathBrownDivisorMellinSeriesTerm
    {s : ℂ} (n : ℕ) :
    Continuous (heathBrownDivisorMellinSeriesTerm s n) := by
  by_cases hn : n = 0
  · subst n
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hPow : Continuous (fun t : ℝ =>
        (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))) := by
      apply Continuous.cpow continuous_const (by fun_prop)
      intro t
      exact Complex.ofReal_mem_slitPlane.mpr hnPos
    unfold heathBrownDivisorMellinSeriesTerm
    simp only [ite_eq_right hn]
    exact (continuous_const.mul continuous_const).mul
      (hPow.mul continuous_Gamma_two_vertical)

theorem norm_heathBrownDivisorMellinSeriesTerm_le
    {s : ℂ} (n : ℕ) (t : ℝ) :
    ‖heathBrownDivisorMellinSeriesTerm s n t‖ ≤
      (n : ℝ) ^ (-s.re - 1) *
        ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := by
  by_cases hn : n = 0
  · subst n
    rw [heathBrownDivisorMellinSeriesTerm, ite_eq_left rfl, norm_zero,
      Nat.cast_zero]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (norm_nonneg _)
  · have hnNatPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hnNatPos
    have hCard : (n.divisors.card : ℝ) ≤ n := by
      exact_mod_cast Nat.card_divisors_le_self n
    let w : ℂ := (2 : ℂ) + (t : ℂ) * I
    have hPowS : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
      simp
    have hPowW : ‖(n : ℂ) ^ (-w)‖ = (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
      simp [w]
    have hCardNonneg : 0 ≤ (n.divisors.card : ℝ) := by positivity
    have hPowSNonneg : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg hnPos.le _
    have hPowWNonneg : 0 ≤ (n : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hnPos.le _
    unfold heathBrownDivisorMellinSeriesTerm
    rw [ite_eq_right hn]
    dsimp only [w]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, hPowS, hPowW]
    have hRest : 0 ≤ (n : ℝ) ^ (-s.re) *
        ((n : ℝ) ^ (-(2 : ℝ)) *
          ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖) :=
      mul_nonneg hPowSNonneg
        (mul_nonneg hPowWNonneg (norm_nonneg _))
    have hMul := mul_le_mul_of_nonneg_right hCard hRest
    calc
      (n.divisors.card : ℝ) * (n : ℝ) ^ (-s.re) *
          ((n : ℝ) ^ (-(2 : ℝ)) *
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖) ≤
        (n : ℝ) * (n : ℝ) ^ (-s.re) *
          ((n : ℝ) ^ (-(2 : ℝ)) *
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖) := by
          simpa only [mul_assoc] using hMul
      _ = (n : ℝ) ^ (-s.re - 1) *
          ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := by
        calc
          (n : ℝ) * (n : ℝ) ^ (-s.re) *
              ((n : ℝ) ^ (-(2 : ℝ)) *
                ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖) =
            (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-s.re) *
              ((n : ℝ) ^ (-(2 : ℝ)) *
                ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖) := by
              rw [Real.rpow_one]
          _ = (n : ℝ) ^ (-s.re - 1) *
              ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := by
            rw [← Real.rpow_add hnPos, ← mul_assoc,
              ← Real.rpow_add hnPos]
            congr 1
            ring_nf

theorem integrable_heathBrownDivisorMellinSeriesTerm
    {s : ℂ} (n : ℕ) :
    Integrable (heathBrownDivisorMellinSeriesTerm s n) := by
  have hMajorant : Integrable (fun t : ℝ =>
      (n : ℝ) ^ (-s.re - 1) *
        ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖) :=
    integrable_Gamma_two_vertical.norm.const_mul _
  exact hMajorant.mono'
    (continuous_heathBrownDivisorMellinSeriesTerm n).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (norm_heathBrownDivisorMellinSeriesTerm_le n))

theorem summable_integral_norm_heathBrownDivisorMellinSeriesTerm
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖heathBrownDivisorMellinSeriesTerm s n t‖) := by
  let G : ℝ := ∫ t : ℝ,
    ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖
  have hPower : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine ((hPower.mul_left G).of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) ?_)
  intro n
  calc
    (∫ t : ℝ, ‖heathBrownDivisorMellinSeriesTerm s n t‖) ≤
        ∫ t : ℝ, (n : ℝ) ^ (-s.re - 1) *
          ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := by
      apply integral_mono
        (integrable_heathBrownDivisorMellinSeriesTerm n).norm
        (integrable_Gamma_two_vertical.norm.const_mul _)
      intro t
      exact norm_heathBrownDivisorMellinSeriesTerm_le n t
    _ = G * (n : ℝ) ^ (-s.re - 1) := by
      rw [integral_const_mul]
      dsimp only [G]
      ring

theorem integral_heathBrownDivisorMellinSeriesTerm
    {s : ℂ} (n : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t : ℝ, heathBrownDivisorMellinSeriesTerm s n t) =
      heathBrownSmoothedDivisorTerm s n := by
  by_cases hn : n = 0
  · subst n
    simp [heathBrownDivisorMellinSeriesTerm,
      heathBrownSmoothedDivisorTerm]
  · have hnNatPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hnNatPos
    have hMellin := inverseMellin_exp_neg (x := (n : ℝ)) hnPos
    unfold heathBrownDivisorMellinSeriesTerm heathBrownSmoothedDivisorTerm
    simp only [ite_eq_right hn]
    rw [show (∫ t : ℝ,
        (n.divisors.card : ℂ) * (n : ℂ) ^ (-s) *
          ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I)) *
            Complex.Gamma ((2 : ℂ) + (t : ℂ) * I))) =
        ((n.divisors.card : ℂ) * (n : ℂ) ^ (-s)) *
          (∫ t : ℝ, (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I)) *
            Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) by
      rw [← MeasureTheory.integral_const_mul]]
    calc
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (((n.divisors.card : ℂ) * (n : ℂ) ^ (-s)) *
            (∫ t : ℝ, (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I)) *
              Complex.Gamma ((2 : ℂ) + (t : ℂ) * I))) =
        ((n.divisors.card : ℂ) * (n : ℂ) ^ (-s)) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            (∫ t : ℝ, (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I)) *
              Complex.Gamma ((2 : ℂ) + (t : ℂ) * I))) := by ring
      _ = ((n.divisors.card : ℂ) * (n : ℂ) ^ (-s)) *
          Real.exp (-(n : ℝ)) := by
        congr 1
      _ = (n.divisors.card : ℂ) * (n : ℂ) ^ (-s) *
          Real.exp (-(n : ℝ)) := by ring

theorem tsum_heathBrownDivisorMellinSeriesTerm_eq
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    (∑' n : ℕ, heathBrownDivisorMellinSeriesTerm s n t) =
      heathBrownDivisorMellinIntegrand s t := by
  let w : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hsw : 1 < (s + w).re := by simp [w]; linarith
  rw [heathBrownDivisorMellinIntegrand,
    riemannZeta_sq_eq_divisorLSeries hsw]
  dsimp only [w]
  unfold LSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [heathBrownDivisorMellinSeriesTerm, LSeries.term]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    unfold heathBrownDivisorMellinSeriesTerm
    rw [ite_eq_right hn, LSeries.term_of_ne_zero hn]
    simp_rw [Complex.cpow_neg]
    rw [show (n : ℂ) ^ (s + ((2 : ℂ) + (t : ℂ) * I)) =
        (n : ℂ) ^ s * (n : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) by
      exact Complex.cpow_add _ _ hnC]
    ring

/-- The exact termwise-integration identity printed immediately before
Heath--Brown's equation (40). -/
theorem heathBrown_smoothed_divisor_eq_right_mellin
    {s : ℂ} (hs : 0 < s.re) :
    heathBrownSmoothedDivisorSeries s =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ t : ℝ, heathBrownDivisorMellinIntegrand s t := by
  have hInterchange := integral_tsum_of_summable_integral_norm
    (fun n => integrable_heathBrownDivisorMellinSeriesTerm n)
    (summable_integral_norm_heathBrownDivisorMellinSeriesTerm hs)
  unfold heathBrownSmoothedDivisorSeries
  rw [show (∑' n : ℕ, heathBrownSmoothedDivisorTerm s n) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∑' n : ℕ, ∫ t : ℝ, heathBrownDivisorMellinSeriesTerm s n t by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    exact (integral_heathBrownDivisorMellinSeriesTerm n).symm]
  rw [hInterchange]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact tsum_heathBrownDivisorMellinSeriesTerm_eq hs t

end MathCollab.Density.Stronger.PointMean
