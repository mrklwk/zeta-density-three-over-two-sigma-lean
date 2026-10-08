module
-- Reversible module-visibility port of the audited development.
/-
Native bounds for the literal DFI Bessel multipliers. Definitions and contour
target: S. McColm, DFIEquation29.lean, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0, copyright 2026.
The direct Gamma estimate uses the proved GammaStrip Apache-2.0 infrastructure
adapted from Conor Grogan f369f267b4dcfebf010c8e7baa2c9602e2960eba.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiZetaGrowth

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_Gamma_voronoi_extended_strip {a t : ℝ}
    (ha : 3/16 ≤ a) (ha' : a ≤ 3/2) :
    ‖Gamma ((a : ℂ) + (t : ℂ)*I)‖ ≤
      72*(1+|t|)*Real.exp (-(Real.pi*|t|)/2) := by
  let E := (1+|t|)*Real.exp (-(Real.pi*|t|)/2)
  have hE : 0 ≤ E := by positivity
  by_cases hhalf : 1/2 ≤ a
  · have h := norm_Gamma_voronoi_strip_sharp (t := t) hhalf ha'
    rw [mul_assoc]
    change ‖Gamma ((a : ℂ) + (t : ℂ)*I)‖ ≤ 72*E
    rw [mul_assoc] at h
    change ‖Gamma ((a : ℂ) + (t : ℂ)*I)‖ ≤ 12*E at h
    nlinarith
  · let z : ℂ := (a : ℂ) + (t : ℂ)*I
    have hz : z ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      norm_num [z] at hr
      linarith
    have hn : 1 ≤ 6*‖z‖ := by
      have h := Complex.re_le_norm z
      simp only [z, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero] at h
      linarith
    have hg := norm_Gamma_voronoi_strip_sharp (a := a+1) (t := t)
      (by linarith) (by linarith)
    have hrec : Gamma (((a+1 : ℝ) : ℂ) + (t : ℂ)*I) = z*Gamma z := by
      convert Gamma_add_one z hz using 1
      congr 1
      simp only [z, ofReal_add, ofReal_one]
      ring
    rw [hrec, norm_mul] at hg
    rw [mul_assoc] at hg
    change ‖z‖ * ‖Gamma z‖ ≤ 12*E at hg
    rw [mul_assoc]
    change ‖Gamma z‖ ≤ 72*E
    nlinarith [norm_nonneg (Gamma z)]

theorem norm_dfiPeriodicArchimedeanFactor_strip_le (q : ℕ) [NeZero q]
    {z : ℂ} (hlo : -(1/2 : ℝ) ≤ z.re) (hhi : z.re ≤ 13/16) :
    ‖dfiPeriodicArchimedeanFactor q (1-z)‖ ≤
      72*(q:ℝ)*(1+|z.im|)*Real.exp (-(Real.pi*|z.im|)/2) := by
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqpos : 0 < (q:ℝ) := by linarith
  have hqp : ‖(q:ℂ)^((1-z)-1)‖ ≤ (q:ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    simpa using Real.rpow_le_rpow_of_exponent_le hq (show ((1-z)-1).re ≤ 1 by
      simp only [sub_re, one_re]; linarith)
  have hpp : ‖(2*Real.pi:ℂ)^(-(1-z))‖ ≤ 1 := by
    rw [show (2*Real.pi:ℂ) = ((2*Real.pi:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · nlinarith [Real.pi_gt_three]
    · simp only [neg_re, sub_re, one_re]; linarith
  have hG := norm_Gamma_voronoi_extended_strip (a := (1-z).re) (t := (1-z).im)
    (by simp only [sub_re, one_re]; linarith)
    (by simp only [sub_re, one_re]; linarith)
  rw [Complex.re_add_im] at hG
  simp only [sub_im, one_im, zero_sub, abs_neg] at hG
  unfold dfiPeriodicArchimedeanFactor
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ((q:ℝ)*1)*(72*(1+|z.im|)*Real.exp (-(Real.pi*|z.im|)/2)) :=
      mul_le_mul (mul_le_mul hqp hpp (norm_nonneg _) (by positivity)) hG
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_dfiVoronoiMinusMultiplier_strip_le (q : ℕ) [NeZero q]
    {z : ℂ} (hlo : -(1/2 : ℝ) ≤ z.re) (hhi : z.re ≤ 13/16) :
    ‖dfiVoronoiMinusMultiplier q z‖ ≤
      10368*(q:ℝ)^3*(1+|z.im|)^2 := by
  have hbranch : ‖cexp (Real.pi*I*(1-z)) + cexp (-Real.pi*I*(1-z))‖ ≤
      2*Real.exp (Real.pi*|z.im|) := by
    have hp : ‖cexp (Real.pi*I*(1-z))‖ ≤ Real.exp (Real.pi*|z.im|) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
        sub_zero, zero_sub, mul_one, sub_im, one_im, add_zero, mul_neg, neg_neg]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) Real.pi_pos.le
    have hm : ‖cexp (-Real.pi*I*(1-z))‖ ≤ Real.exp (Real.pi*|z.im|) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [mul_re, mul_im, neg_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, zero_sub, mul_one, sub_im, one_im, add_zero,
        neg_mul, neg_neg]
      nlinarith [neg_le_abs z.im, Real.pi_pos]
    exact (norm_add_le _ _).trans (by linarith)
  have hF := norm_dfiPeriodicArchimedeanFactor_strip_le q hlo hhi
  unfold dfiVoronoiMinusMultiplier
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (q:ℝ)*(72*(q:ℝ)*(1+|z.im|)*Real.exp (-(Real.pi*|z.im|)/2))^2 *
        (2*Real.exp (Real.pi*|z.im|)) := by gcongr
    _ = (10368*(q:ℝ)^3*(1+|z.im|)^2) *
        (Real.exp (-(Real.pi*|z.im|)/2)^2 * Real.exp (Real.pi*|z.im|)) := by ring
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(-(Real.pi*|z.im|)/2)+Real.pi*|z.im| = 0 by ring,
        Real.exp_zero, mul_one]

theorem norm_dfiVoronoiPlusMultiplier_strip_le (q : ℕ) [NeZero q]
    {z : ℂ} (hlo : -(1/2 : ℝ) ≤ z.re) (hhi : z.re ≤ 13/16) :
    ‖dfiVoronoiPlusMultiplier q z‖ ≤
      10368*(q:ℝ)^3*(1+|z.im|)^2 := by
  have hF := norm_dfiPeriodicArchimedeanFactor_strip_le q hlo hhi
  have he : Real.exp (-(Real.pi*|z.im|)/2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := abs_nonneg z.im
    nlinarith [Real.pi_pos]
  have hF' : ‖dfiPeriodicArchimedeanFactor q (1-z)‖ ≤ 72*(q:ℝ)*(1+|z.im|) :=
    hF.trans (mul_le_of_le_one_right (by positivity) he)
  unfold dfiVoronoiPlusMultiplier
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, norm_ofNat]
  calc
    _ ≤ 2*(q:ℝ)*(72*(q:ℝ)*(1+|z.im|))^2 := by gcongr
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
