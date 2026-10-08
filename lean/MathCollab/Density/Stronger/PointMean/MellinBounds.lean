module
-- Reversible module-visibility port of the audited development.
/-
Selected harmless-term bounds adapted from Scott McColm,
PointMeanMellinBounds.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The residue estimate uses the proved explicit local DigammaLog error and
Gamma kernel. No source Gamma displacement or moment bound is assumed.
-/
public import MathCollab.Density.Stronger.PointMean.MovingPole
public import MathCollab.Density.Stronger.PointMean.DivisorMellin
public import MathCollab.Density.Stronger.PointMean.GammaKernel
public import Mathlib.Analysis.SpecialFunctions.Exp

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter ArithmeticFunction
open MathCollab.Density.Stronger.Fourth.Digamma
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- A concrete absolute constant dominating the exponentially smoothed
divisor series. -/
noncomputable def heathBrownSmoothedDivisorMajorant : ℝ :=
  ∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ))

theorem summable_heathBrownSmoothedDivisorMajorant :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ))) := by
  simpa only [pow_one, one_mul, neg_one_mul] using
    (Real.summable_pow_mul_exp_neg_nat_mul 1 (show (0 : ℝ) < 1 by norm_num))

theorem heathBrownSmoothedDivisorMajorant_nonneg :
    0 ≤ heathBrownSmoothedDivisorMajorant := by
  unfold heathBrownSmoothedDivisorMajorant
  exact tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg' n) (Real.exp_pos _).le

theorem norm_heathBrownSmoothedDivisorTerm_le
    {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖heathBrownSmoothedDivisorTerm s n‖ ≤
      (n : ℝ) * Real.exp (-(n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp [heathBrownSmoothedDivisorTerm]
  · have hnNatPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hnNatPos
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnNatPos
    have hCard : (n.divisors.card : ℝ) ≤ n := by
      exact_mod_cast Nat.card_divisors_le_self n
    have hPow : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
      simp
    have hPowOne : (n : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnOne (by linarith)
    unfold heathBrownSmoothedDivisorTerm
    rw [ite_eq_right hn, norm_mul, norm_mul, Complex.norm_natCast, hPow]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hCardNonneg : 0 ≤ (n.divisors.card : ℝ) := by positivity
    have hExpNonneg : 0 ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
    calc
      (n.divisors.card : ℝ) * (n : ℝ) ^ (-s.re) *
          Real.exp (-(n : ℝ)) ≤
        (n : ℝ) * 1 * Real.exp (-(n : ℝ)) := by
          gcongr
      _ = (n : ℝ) * Real.exp (-(n : ℝ)) := by ring

theorem summable_norm_heathBrownSmoothedDivisorTerm
    {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ => ‖heathBrownSmoothedDivisorTerm s n‖) :=
  summable_heathBrownSmoothedDivisorMajorant.of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_heathBrownSmoothedDivisorTerm_le hs)

theorem norm_heathBrownSmoothedDivisorSeries_le
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖heathBrownSmoothedDivisorSeries s‖ ≤
      heathBrownSmoothedDivisorMajorant := by
  unfold heathBrownSmoothedDivisorSeries heathBrownSmoothedDivisorMajorant
  calc
    ‖∑' n : ℕ, heathBrownSmoothedDivisorTerm s n‖ ≤
        ∑' n : ℕ, ‖heathBrownSmoothedDivisorTerm s n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_heathBrownSmoothedDivisorTerm hs)
    _ ≤ ∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ)) :=
      (summable_norm_heathBrownSmoothedDivisorTerm hs).tsum_le_tsum
        (norm_heathBrownSmoothedDivisorTerm_le hs)
        summable_heathBrownSmoothedDivisorMajorant

theorem exists_norm_Gamma_heathBrown_residue_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (a v : ℝ), 5 / 4 ≤ a → a ≤ 3 / 2 →
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤ C * Real.exp (-|v|) := by
  refine ⟨72, by norm_num, ?_⟩
  intro a v ha ha'
  apply (norm_Gamma_positive_strip_strong (by linarith) ha').trans
  gcongr
  linarith [abs_nonneg v]

/-- Gamma decay at the moving zeta pole `1-s`, uniformly for the small
positive displacement used by Heath--Brown. -/
theorem exists_norm_Gamma_heathBrown_movingPole_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta v : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖Complex.Gamma
          (((1 / 2 - delta : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) := by
  obtain ⟨B, hB, hStrip⟩ :=
    exists_norm_Gamma_heathBrown_residue_strip_le
  let C : ℝ := 4 * B
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro delta v hdelta hdeltaUpper
  let p : ℂ := ((1 / 2 - delta : ℝ) : ℂ) + (v : ℂ) * I
  have hpRe : p.re = 1 / 2 - delta := by simp [p]
  have hpNonzero : p ≠ 0 := by
    intro hp
    have hre := congrArg Complex.re hp
    rw [hpRe] at hre
    norm_num at hre
    linarith
  have harg : p + 1 =
      ((3 / 2 - delta : ℝ) : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp [p]
    ring
  have hUpper :
      ‖Complex.Gamma (p + 1)‖ ≤ B * Real.exp (-|v|) := by
    rw [harg]
    exact hStrip (3 / 2 - delta) v (by linarith) (by linarith)
  have hRec := Complex.Gamma_add_one p hpNonzero
  have hRecNorm : ‖Complex.Gamma (p + 1)‖ =
      ‖p‖ * ‖Complex.Gamma p‖ := by
    rw [hRec, norm_mul]
  have hpNormLower : (1 / 4 : ℝ) ≤ ‖p‖ := by
    have hre := Complex.abs_re_le_norm p
    rw [hpRe, abs_of_pos (by linarith : 0 < 1 / 2 - delta)] at hre
    linarith
  have hGamma : ‖Complex.Gamma p‖ ≤
      4 * (B * Real.exp (-|v|)) := by
    rw [hRecNorm] at hUpper
    nlinarith [norm_nonneg (Complex.Gamma p), Real.exp_pos (-|v|)]
  simpa only [p, C, mul_assoc] using hGamma

/-- Explicit large-height bound sufficient for the decaying residue factor. -/
theorem norm_digamma_small_strip_le_linear {z : ℂ}
    (hz : 0 < z.re) (hz' : z.re ≤ 1 / 2) (hy : 1 ≤ |z.im|) :
    ‖Complex.digamma z‖ ≤ |z.im| + 8 := by
  have hn : 1 ≤ ‖z‖ := hy.trans (Complex.abs_im_le_norm z)
  have hlog : Real.log ‖z‖ ≤ |z.im| := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖z‖)
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz] at hnorm
    linarith
  have hl : ‖Complex.log z‖ ≤ |z.im| + 4 := by
    calc
      _ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = Real.log ‖z‖ + |Complex.arg z| := by
        rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hn)]
      _ ≤ |z.im| + 4 := by
        linarith [Complex.abs_arg_le_pi z, Real.pi_le_four]
  have hd := norm_digamma_sub_log_le hz hy
  have he : 4 / |z.im| ≤ (4 : ℝ) :=
    (div_le_iff₀ (zero_lt_one.trans_le hy)).2 (by linarith)
  calc
    _ = ‖(Complex.digamma z - Complex.log z) + Complex.log z‖ := by rw [sub_add_cancel]
    _ ≤ ‖Complex.digamma z - Complex.log z‖ + ‖Complex.log z‖ := norm_add_le _ _
    _ ≤ |z.im| + 8 := by linarith

/-- Uniform bound for the actual derivative residue at the moving double pole. -/
theorem exists_norm_heathBrownMovingPoleResidue_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖heathBrownMovingPoleResidue
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  obtain ⟨B, hB, hGamma⟩ := exists_norm_Gamma_heathBrown_movingPole_le
  let R : ℝ := ‖deriv riemannZetaPoleRemoved 0‖
  let C : ℝ := B * (10 + 2 * R)
  refine ⟨C, by dsimp [C, R]; positivity, ?_⟩
  intro delta t hdelta hdeltaUpper ht
  let s : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I
  let p : ℂ := heathBrownMovingPole s
  have hp : p = ((1 / 2 - delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [p, s, heathBrownMovingPole]
    ring
  have hpRe : p.re = 1 / 2 - delta := by rw [hp]; simp
  have hpIm : |p.im| = t := by rw [hp]; simp [abs_of_nonneg (by linarith : 0 ≤ t)]
  have hpPos : 0 < p.re := by rw [hpRe]; linarith
  have hGammaP : ‖Complex.Gamma p‖ ≤ B * Real.exp (-t) := by
    rw [hp]
    simpa [abs_of_nonneg (by linarith : 0 ≤ t)] using
      hGamma delta (-t) hdelta hdeltaUpper
  have hDigammaP : ‖Complex.digamma p‖ ≤ t + 8 := by
    simpa only [hpIm] using norm_digamma_small_strip_le_linear hpPos
      (by rw [hpRe]; linarith) (by rw [hpIm]; linarith)
  have hExp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hTExp : t * Real.exp (-t) ≤ 1 := by
    have h := Real.mul_exp_neg_le_exp_neg_one t
    have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have hResidueEq := heathBrownMovingPoleResidue_eq (s := s) hpPos
  change ‖heathBrownMovingPoleResidue s‖ ≤ C
  rw [hResidueEq]
  calc
    ‖Complex.Gamma p * Complex.digamma p +
        2 * Complex.Gamma p * deriv riemannZetaPoleRemoved 0‖ ≤
      ‖Complex.Gamma p‖ * ‖Complex.digamma p‖ + 2 * ‖Complex.Gamma p‖ * R := by
        simpa [R] using norm_add_le (Complex.Gamma p * Complex.digamma p)
          (2 * Complex.Gamma p * deriv riemannZetaPoleRemoved 0)
    _ ≤ (B * Real.exp (-t)) * (t + 8) + 2 * (B * Real.exp (-t)) * R := by
      gcongr
    _ = B * (t * Real.exp (-t) + 8 * Real.exp (-t) + 2 * R * Real.exp (-t)) := by ring
    _ ≤ B * (1 + 8 + 2 * R * 1) := by
      have hR : 0 ≤ R := norm_nonneg _
      apply mul_le_mul_of_nonneg_left _ hB.le
      nlinarith [mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ 2 * R)]
    _ ≤ C := by dsimp only [C]; nlinarith


end MathCollab.Density.Stronger.PointMean
