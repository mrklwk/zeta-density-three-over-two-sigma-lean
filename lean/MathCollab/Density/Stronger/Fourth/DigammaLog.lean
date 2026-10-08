module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/LICENSE-MIT-0 and
../../../../../third_party/twelfth/DIGAMMA_PORT_MANIFEST.json.
The imported DigammaSeries preserves its separate Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.DigammaSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# A uniform logarithmic approximation to the actual digamma function

The reciprocal series is compared with the principal logarithm on each
unit interval in the right half-plane. This is the leading term of DLMF
5.11.2, with an explicit vertical error; no Stirling estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter Finset MeasureTheory Set Topology

namespace MathCollab.Density.Stronger.Fourth.Digamma

theorem shift_ne_zero {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    z + x ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [add_re, ofReal_re, zero_re] at hre
  linarith

theorem integral_shift_inv {z : ℂ} (hz : 0 < z.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, (z + x)⁻¹) = Complex.log (z + b) - Complex.log (z + a) := by
  have hc : ContinuousOn (fun x : ℝ => (z + x)⁻¹) (Icc a b) :=
    (continuous_const.add Complex.continuous_ofReal).continuousOn.inv₀
      (fun x hx => shift_ne_zero hz (ha.trans hx.1))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt ?_
    (hc.intervalIntegrable_of_Icc hab)
  intro x hx
  have hx0 : 0 ≤ x := ha.trans ((uIcc_of_le hab ▸ hx).1)
  have hslit : z + (x : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [add_re, ofReal_re]
    linarith
  simpa using ((Complex.hasDerivAt_log hslit).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal

theorem norm_shift_mono {z : ℂ} (hz : 0 < z.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : ‖z + a‖ ≤ ‖z + b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, ofReal_re,
    ofReal_im, add_zero]
  nlinarith

/-- One unit-interval sum--integral error, with a height-sensitive denominator. -/
theorem norm_reciprocal_log_step_le {z : ℂ} (hz : 0 < z.re)
    (hy : 0 < |z.im|) (n : ℕ) :
    ‖(z + n)⁻¹ - (Complex.log (z + (n + 1 : ℕ)) - Complex.log (z + n))‖ ≤
      2 / ((n : ℝ) + |z.im|) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hint : IntervalIntegrable (fun x : ℝ => (z + x)⁻¹) volume n (n + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    exact (continuous_const.add Complex.continuous_ofReal).continuousOn.inv₀
      (fun x hx => shift_ne_zero hz (hn.trans hx.1))
  have heq : (z + n)⁻¹ - (Complex.log (z + (n + 1 : ℕ)) - Complex.log (z + n)) =
      ∫ x in (n : ℝ)..(n : ℝ) + 1, ((z + n)⁻¹ - (z + x)⁻¹) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
      integral_shift_inv hz hn (by linarith)]
    simp
  rw [heq]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (n : ℝ)) (b := (n : ℝ) + 1)
    (f := fun x : ℝ => (z + n)⁻¹ - (z + x)⁻¹)
    (C := 2 / ((n : ℝ) + |z.im|) ^ 2) ?_
  · simpa using hbound
  intro x hx
  change ‖(z + n)⁻¹ - (z + x)⁻¹‖ ≤ 2 / ((n : ℝ) + |z.im|) ^ 2
  rw [uIoc_of_le (by linarith : (n : ℝ) ≤ n + 1)] at hx
  have hnx : (n : ℝ) ≤ x := hx.1.le
  have hx0 := hn.trans hnx
  have hnz : z + n ≠ 0 := shift_ne_zero hz hn
  have hxz : z + x ≠ 0 := shift_ne_zero hz hx0
  have hnorm : 0 < ‖z + n‖ := norm_pos_iff.mpr hnz
  have hmono := norm_shift_mono hz hn hnx
  simp only [Complex.ofReal_natCast] at hmono
  have hden : ((n : ℝ) + |z.im|) ^ 2 ≤ 2 * ‖z + n‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, add_im, natCast_re, natCast_im, add_zero]
    nlinarith [sq_nonneg ((n : ℝ) - |z.im|), sq_abs z.im]
  have hdiff : (z + n)⁻¹ - (z + x)⁻¹ = ((x - n : ℝ) : ℂ) / ((z + n) * (z + x)) := by
    push_cast
    field_simp
    ring
  rw [hdiff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hnx)]
  have hbase : 0 < (n : ℝ) + |z.im| := add_pos_of_nonneg_of_pos hn hy
  apply (div_le_div_iff₀ (mul_pos hnorm (hnorm.trans_le hmono))
    (sq_pos_of_pos hbase)).mpr
  have hnum : x - n ≤ 1 := by linarith [hx.2]
  have hprod : ‖z + n‖ ^ 2 ≤ ‖z + n‖ * ‖z + x‖ := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hnum (sq_nonneg ((n : ℝ) + |z.im|))]

theorem sum_reciprocal_sq_le {y : ℝ} (hy : 1 ≤ y) (N : ℕ) :
    (∑ n ∈ range N, 2 / ((n : ℝ) + y) ^ 2) ≤ 4 / y := by
  have hstep (n : ℕ) : 2 / ((n : ℝ) + y) ^ 2 ≤
      4 * (((n : ℝ) + y)⁻¹ - ((n : ℝ) + y + 1)⁻¹) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : 0 < (n : ℝ) + y := by linarith
    have hp1 : 0 < (n : ℝ) + y + 1 := by linarith
    field_simp
    nlinarith
  calc
    _ ≤ ∑ n ∈ range N, 4 * (((n : ℝ) + y)⁻¹ - ((n : ℝ) + y + 1)⁻¹) :=
      sum_le_sum (fun n _ => hstep n)
    _ = 4 * (y⁻¹ - ((N : ℝ) + y)⁻¹) := by
      rw [← mul_sum]
      congr 1
      induction N with
      | zero => simp
      | succ N ih => rw [sum_range_succ, ih]; push_cast; ring
    _ ≤ 4 / y := by
      have hnonneg : 0 ≤ ((N : ℝ) + y)⁻¹ := inv_nonneg.mpr (by positivity)
      rw [div_eq_mul_inv]
      linarith

/-- Finite logarithmic comparison, uniform in the truncation length. -/
theorem norm_sum_reciprocal_sub_log_le {z : ℂ} (hz : 0 < z.re)
    (hy : 1 ≤ |z.im|) (N : ℕ) :
    ‖(∑ n ∈ range N, (z + n)⁻¹) -
      (Complex.log (z + N) - Complex.log z)‖ ≤ 4 / |z.im| := by
  have heq : (∑ n ∈ range N, (z + n)⁻¹) -
      (Complex.log (z + N) - Complex.log z) =
      ∑ n ∈ range N, ((z + n)⁻¹ -
        (Complex.log (z + (n + 1 : ℕ)) - Complex.log (z + n))) := by
    induction N with
    | zero => simp
    | succ N ih => simp only [sum_range_succ]; rw [← ih]; ring
  rw [heq]
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun n _ =>
    norm_reciprocal_log_step_le hz (lt_of_lt_of_le zero_lt_one hy) n)).trans
      (sum_reciprocal_sq_le hy N))

/-- Shifting a large positive integer by a fixed right-half-plane point
does not change its logarithm asymptotically; the principal branch is exact. -/
theorem tendsto_log_nat_shift_sub_log {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => Complex.log (z + N) - (Real.log N : ℂ))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have harg : Tendsto (fun N : ℕ => 1 + z * (N : ℂ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hinv.const_mul z)
  have hlog : Tendsto (fun N : ℕ => Complex.log (1 + z * (N : ℂ)⁻¹))
      atTop (𝓝 0) := by
    simpa using! (Complex.hasDerivAt_log
      (by simp : (1 : ℂ) ∈ Complex.slitPlane)).continuousAt.tendsto.comp harg
  apply hlog.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNp.ne'
  have hfactor : z + N = (N : ℂ) * (1 + z * (N : ℂ)⁻¹) := by
    field_simp
    ring
  have hne : 1 + z * (N : ℂ)⁻¹ ≠ 0 := by
    intro h
    have hzN := shift_ne_zero hz hNp.le
    apply hzN
    simpa [h] using hfactor
  have hmul := Complex.log_ofReal_mul hNp hne
  simp only [Complex.ofReal_natCast] at hmul
  rw [hfactor, hmul]
  ring

/-- The actual digamma function has a uniform explicit logarithmic error
throughout the right half-plane at either sign of height. -/
theorem norm_digamma_sub_log_le {z : ℂ} (hz : 0 < z.re)
    (hy : 1 ≤ |z.im|) : ‖Complex.digamma z - Complex.log z‖ ≤ 4 / |z.im| := by
  have hseries := (hasSum_digamma_of_re_pos hz).tendsto_sum_nat
  have hharmonic : Tendsto
      (fun N : ℕ => ((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_sub, Complex.ofReal_ratCast] using
      (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
  have hpsi : Tendsto
      (fun N : ℕ => (Real.log N : ℂ) - ∑ n ∈ range N, (z + n)⁻¹)
      atTop (𝓝 (Complex.digamma z)) := by
    have h := hseries.sub hharmonic
    simp only [add_sub_cancel_right] at h
    convert h using 1
    ext N
    rw [sum_sub_distrib, sum_inv_natCast_add_one]
    ring
  have herror : Tendsto
      (fun N : ℕ => (∑ n ∈ range N, (z + n)⁻¹) -
        (Complex.log (z + N) - Complex.log z))
      atTop (𝓝 (Complex.log z - Complex.digamma z)) := by
    have h := (tendsto_const_nhds (x := Complex.log z)).sub
      (hpsi.add (tendsto_log_nat_shift_sub_log hz))
    simp only [add_zero] at h
    convert h using 1
    ext N
    ring
  rw [norm_sub_rev]
  exact le_of_tendsto herror.norm (Eventually.of_forall
    (fun N => norm_sum_reciprocal_sub_log_le hz hy N))

/-- The real part needed for the critical-line Gamma phase, retaining the
explicit dependence on the real coordinate. -/
theorem abs_re_digamma_sub_log_im_le {z : ℂ} (hz : 0 < z.re)
    (hy : 1 ≤ |z.im|) :
    |(Complex.digamma z).re - Real.log (|z.im|)| ≤ (4 + z.re) / |z.im| := by
  have hy0 : 0 < |z.im| := lt_of_lt_of_le zero_lt_one hy
  have hynorm := Complex.abs_im_le_norm z
  have hn0 := hy0.trans_le hynorm
  have hnup : ‖z‖ ≤ z.re + |z.im| := by
    simpa only [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im z
  have hlog0 : 0 ≤ Real.log ‖z‖ - Real.log |z.im| :=
    sub_nonneg.mpr (Real.log_le_log hy0 hynorm)
  have hlogup : Real.log ‖z‖ - Real.log |z.im| ≤ z.re / |z.im| := by
    have h := Real.log_le_sub_one_of_pos (div_pos hn0 hy0)
    rw [Real.log_div hn0.ne' hy0.ne'] at h
    have hratio := (div_le_div_iff_of_pos_right hy0).mpr hnup
    rw [add_div, div_self hy0.ne'] at hratio
    linarith
  have hmain : |(Complex.digamma z).re - Real.log ‖z‖| ≤ 4 / |z.im| := by
    simpa only [Complex.sub_re, Complex.log_re] using
      (Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)).trans
        (norm_digamma_sub_log_le hz hy)
  calc
    _ = |((Complex.digamma z).re - Real.log ‖z‖) +
        (Real.log ‖z‖ - Real.log |z.im|)| := by congr 1; ring
    _ ≤ |(Complex.digamma z).re - Real.log ‖z‖| +
        |Real.log ‖z‖ - Real.log (|z.im|)| := abs_add_le _ _
    _ ≤ 4 / |z.im| + z.re / |z.im| := by
      rw [abs_of_nonneg hlog0]
      exact add_le_add hmain hlogup
    _ = _ := by rw [add_div]

end MathCollab.Density.Stronger.Fourth.Digamma
