module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice from ZetaBesselK0Decay.lean,
revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain
Apache-2.0 attribution. No Voronoi identity or analytic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselK0

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem dfiBesselK0_nonneg (x : ℝ) : 0 ≤ dfiBesselK0 x :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem dfiBesselK0_le_exp_mul_half {x : ℝ} (hx : 0 < x) :
    dfiBesselK0 x ≤ Real.exp (-x / 2) * dfiBesselK0 (x / 2) := by
  have hh : IntegrableOn (fun t : ℝ => Real.exp (-(x / 2) * Real.cosh t)) (Ioi 0) :=
    integrableOn_dfiBesselK0_integrand (by positivity)
  have hp (t : ℝ) : Real.exp (-x * Real.cosh t) ≤
      Real.exp (-x / 2) * Real.exp (-(x / 2) * Real.cosh t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [one_add_sq_div_two_le_cosh t, sq_nonneg t]
  have h := setIntegral_mono (integrableOn_dfiBesselK0_integrand hx)
    (hh.const_mul (Real.exp (-x / 2))) hp
  simpa only [integral_const_mul, dfiBesselK0] using h

theorem abs_dfiBesselK0_exp_le {x : ℝ} (hx : 2 ≤ x) :
    |dfiBesselK0 x| ≤ 2 * Real.exp (-x / 2) := by
  have hx0 : 0 < x := by linarith
  have hsqrt : 1 ≤ Real.sqrt (x / 2) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith)
  have hb : dfiBesselK0 (x / 2) ≤ 2 := by
    apply ((le_abs_self _).trans (abs_dfiBesselK0_le_two_div_sqrt (by positivity))).trans
    exact div_le_self (by norm_num) hsqrt
  rw [abs_of_nonneg (dfiBesselK0_nonneg x)]
  apply (dfiBesselK0_le_exp_mul_half hx0).trans
  nlinarith [Real.exp_pos (-x / 2)]

theorem exp_neg_le_factorial_div_pow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.exp (-x) ≤ (k.factorial : ℝ) / x ^ k := by
  have h := Real.pow_div_factorial_le_exp x hx.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hp : 0 < x ^ k := pow_pos hx k
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos x) hp).mpr
  have hmul := (div_le_iff₀ hf).mp h
  nlinarith

def zetaBesselK0PowerConstant (k : ℕ) : ℝ :=
  2 * 2 ^ (2 * k) * ((2 * k).factorial : ℝ)

theorem zetaBesselK0PowerConstant_pos (k : ℕ) : 0 < zetaBesselK0PowerConstant k := by
  unfold zetaBesselK0PowerConstant
  positivity

theorem abs_dfiBesselK0_pow_le {x : ℝ} (hx : 2 ≤ x) (k : ℕ) :
    |dfiBesselK0 x| ≤ zetaBesselK0PowerConstant k / (x ^ 2) ^ k := by
  have he := exp_neg_le_factorial_div_pow (show 0 < x / 2 by linarith) (2 * k)
  rw [← neg_div] at he
  apply (abs_dfiBesselK0_exp_le hx).trans
  calc
    _ ≤ 2 * (((2 * k).factorial : ℝ) / (x / 2) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by
      unfold zetaBesselK0PowerConstant
      rw [div_pow, div_div_eq_mul_div, pow_mul]
      ring

/-- The source's coarse positive support links the Bessel argument to
both physical height and the positive arithmetic index. -/
theorem abs_dfiBesselK0_source_le {T x : ℝ} (hT : 16 ≤ T) (hx : T / 16 ≤ x)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    |dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n))| ≤
      zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hx1 : 1 ≤ x := by linarith
  have hsq : (4 * Real.pi * Real.sqrt (x * n)) ^ 2 = 16 * Real.pi ^ 2 * (x * n) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hbase : T * n ≤ (4 * Real.pi * Real.sqrt (x * n)) ^ 2 := by
    rw [hsq]
    have hxT : T ≤ 16 * x := by linarith
    have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right hxT hn0.le,
      mul_nonneg (sub_nonneg.mpr hpi) (show 0 ≤ x * n by positivity)]
  have hy : 2 ≤ 4 * Real.pi * Real.sqrt (x * n) := by
    have hy0 : 0 ≤ 4 * Real.pi * Real.sqrt (x * n) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hn1 (show 0 ≤ T by linarith)]
  apply (abs_dfiBesselK0_pow_le hy k).trans
  rw [← mul_pow]
  exact div_le_div_of_nonneg_left (zetaBesselK0PowerConstant_pos k).le
    (pow_pos (by positivity : 0 < T * n) k)
    (pow_le_pow_left₀ (by positivity) hbase k)

end MathCollab.Density.Stronger.Atkinson
