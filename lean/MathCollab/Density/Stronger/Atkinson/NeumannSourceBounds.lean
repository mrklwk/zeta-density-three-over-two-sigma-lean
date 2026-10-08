module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannSourceBounds.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannTwoTermExpansion
public import MathCollab.Density.Stronger.Atkinson.BesselY0Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Measurability and physical-source bounds for the Neumann remainder

The literal kernel and both retained oscillatory terms are measurable.
The actual Bessel argument is linked to height and divisor index;
its quadratic expansion error has the summable n^(-5/4) weight.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem measurable_dfiBesselY0 : Measurable dfiBesselY0 := by
  have ho : StronglyMeasurable (fun p : ℝ × ℝ =>
      Complex.exp (I * (p.1 * Real.cos p.2))) := (by fun_prop : Continuous _).stronglyMeasurable
  have ht : StronglyMeasurable (fun p : ℝ × ℝ =>
      Real.exp (-p.1 * p.2) / Real.sqrt (1 + p.2 ^ 2)) := by
    apply Continuous.stronglyMeasurable
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro p
      exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hos : Measurable dfiBesselY0Osc := by
    have h := Complex.measurable_im.comp
      (ho.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (Real.pi / 2)))).measurable
    unfold dfiBesselY0Osc
    simp only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    simpa only [Function.comp_def] using! h
  have hts : Measurable dfiBesselY0Tail :=
    (ht.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable
  exact measurable_const.mul (hos.sub hts)

theorem measurable_neumannTwoTerm : Measurable neumannTwoTerm := by
  unfold neumannTwoTerm
  fun_prop

theorem neumann_source_argument_bounds {T x : ℝ} (hT : 16 ≤ T) (hx : T / 16 ≤ x)
    {n : ℕ} (hn : 0 < n) :
    T * n ≤ (4 * Real.pi * Real.sqrt (x * n)) ^ 2 ∧
      1 ≤ 4 * Real.pi * Real.sqrt (x * n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hx1 : 1 ≤ x := by linarith
  have hsq : (4 * Real.pi * Real.sqrt (x * n)) ^ 2 = 16 * Real.pi ^ 2 * (x * n) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hb : T * n ≤ (4 * Real.pi * Real.sqrt (x * n)) ^ 2 := by
    rw [hsq]
    have hxT : T ≤ 16 * x := by linarith
    have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right hxT hn0.le,
      mul_nonneg (sub_nonneg.mpr hpi) (show 0 ≤ x * n by positivity)]
  refine ⟨hb, ?_⟩
  have hy0 : 0 ≤ 4 * Real.pi * Real.sqrt (x * n) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hn1 (show 0 ≤ T by linarith)]

theorem abs_neumann_source_remainder_le {T x : ℝ} (hT : 16 ≤ T) (hx : T / 16 ≤ x)
    {n : ℕ} (hn : 0 < n) :
    |dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) -
      neumannTwoTerm (4 * Real.pi * Real.sqrt (x * n))| ≤
        neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨hbase, hy1⟩ := neumann_source_argument_bounds hT hx hn
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by positivity
  have hy0 : 0 < 4 * Real.pi * Real.sqrt (x * n) := by linarith
  apply (abs_dfiBesselY0_sub_neumannTwoTerm_le hy0).trans
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hT0 hn0) hbase
    (by norm_num : -(5 / 4 : ℝ) ≤ 0)
  have he : ((4 * Real.pi * Real.sqrt (x * n)) ^ 2) ^ (-(5 / 4 : ℝ)) =
      (4 * Real.pi * Real.sqrt (x * n)) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hy0.le]
    norm_num
  rw [he, Real.mul_rpow hT0.le hn0.le] at hp
  have h := mul_le_mul_of_nonneg_left hp neumannTwoTermErrorConstant_pos.le
  simpa only [mul_assoc] using h

theorem abs_dfiBesselY0_source_le_seven {T x : ℝ} (hT : 16 ≤ T) (hx : T / 16 ≤ x)
    {n : ℕ} (hn : 0 < n) :
    |dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n))| ≤ 7 := by
  have hy := (neumann_source_argument_bounds hT hx hn).2
  have hy0 : 0 < 4 * Real.pi * Real.sqrt (x * n) := by linarith
  exact (abs_dfiBesselY0_le_seven_div_sqrt hy0).trans
    (div_le_self (by norm_num) (Real.one_le_sqrt.2 hy))

theorem neumann_source_height_absorb {T : ℝ} (hT : 1 ≤ T) :
    T * T ^ (-(5 / 4 : ℝ)) ≤ 1 := by
  have ht0 : 0 < T := by linarith
  have h := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : -(5 / 4 : ℝ) ≤ -1)
  have hh := mul_le_mul_of_nonneg_left h ht0.le
  simpa only [Real.rpow_neg_one, mul_inv_cancel₀ ht0.ne'] using hh

end MathCollab.Density.Stronger.Atkinson
