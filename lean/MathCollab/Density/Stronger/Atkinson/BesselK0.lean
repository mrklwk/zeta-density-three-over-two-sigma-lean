module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselKernel.lean,
exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/BESSEL_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain
Apache-2.0 attribution. No Estermann or general-modulus source closure is imported.
-/
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Real.Pi.Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open scoped Topology Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- The positive-sign order-zero kernel, in the classical representation
`K₀(x) = ∫₀∞ exp (-x cosh t) dt` for `x > 0`. -/
noncomputable def dfiBesselK0 (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t)

/-- The elementary quadratic lower bound for the hyperbolic cosine. -/
theorem one_add_sq_div_two_le_cosh (t : ℝ) :
    1 + t ^ 2 / 2 ≤ Real.cosh t := by
  rw [Real.cosh_eq_tsum]
  have hsummable := (Real.hasSum_cosh t).summable
  have hnonneg : ∀ n : ℕ, 0 ≤ t ^ (2 * n) / (2 * n).factorial := by
    intro n
    rw [show 2 * n = n * 2 by omega, pow_mul]
    positivity
  have hpartial := hsummable.sum_le_tsum (s := Finset.range 2)
    (fun n hn => hnonneg n)
  norm_num [Finset.sum_range_succ] at hpartial ⊢
  exact hpartial

/-- Gaussian domination of the positive-sign Bessel integrand. -/
theorem dfiBesselK0_integrand_le_gaussian
    {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    Real.exp (-x * Real.cosh t) ≤ Real.exp (-(x / 2) * t ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hcosh := one_add_sq_div_two_le_cosh t
  calc
    -x * Real.cosh t ≤ -x * (1 + t ^ 2 / 2) := by
      exact mul_le_mul_of_nonpos_left hcosh (neg_nonpos.mpr hx)
    _ ≤ -(x / 2) * t ^ 2 := by
      nlinarith

/-- The defining integral of `dfiBesselK0` is absolutely integrable for a
positive argument. -/
theorem integrableOn_dfiBesselK0_integrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-x * Real.cosh t)) (Set.Ioi 0) := by
  have hgauss : IntegrableOn
      (fun t : ℝ => Real.exp (-(x / 2) * t ^ 2)) (Set.Ioi 0) := by
    exact (integrable_exp_neg_mul_sq (by positivity : 0 < x / 2)).integrableOn
  refine hgauss.mono' ?_ ?_
  · exact (Real.continuous_exp.comp
      (continuous_const.mul Real.continuous_cosh)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact dfiBesselK0_integrand_le_gaussian hx.le t

/-- DFI's source-strength trivial bound `K₀(x) ≪ x⁻¹ᐟ²`, with an explicit
The constant. -/
theorem abs_dfiBesselK0_le {x : ℝ} (hx : 0 < x) :
    |dfiBesselK0 x| ≤ Real.sqrt (Real.pi / (x / 2)) / 2 := by
  have hInt := integrableOn_dfiBesselK0_integrand hx
  have hGauss : IntegrableOn
      (fun t : ℝ => Real.exp (-(x / 2) * t ^ 2)) (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < x / 2)).integrableOn
  have hnonneg : 0 ≤ dfiBesselK0 x := by
    unfold dfiBesselK0
    exact integral_nonneg fun _ => (Real.exp_pos _).le
  rw [abs_of_nonneg hnonneg]
  unfold dfiBesselK0
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t) ≤
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x / 2) * t ^ 2) := by
      exact setIntegral_mono hInt hGauss fun t =>
        dfiBesselK0_integrand_le_gaussian hx.le t
    _ = Real.sqrt (Real.pi / (x / 2)) / 2 := integral_gaussian_Ioi (x / 2)

/-- A simpler power form of the preceding estimate. -/
theorem abs_dfiBesselK0_le_two_div_sqrt {x : ℝ} (hx : 0 < x) :
    |dfiBesselK0 x| ≤ 2 / Real.sqrt x := by
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hquotPos : 0 ≤ Real.pi / (x / 2) := by positivity
  have hsquareA : Real.sqrt (Real.pi / (x / 2)) ^ 2 =
      Real.pi / (x / 2) := Real.sq_sqrt hquotPos
  have hsquareX : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hprodNonneg :
      0 ≤ Real.sqrt (Real.pi / (x / 2)) * Real.sqrt x := by positivity
  have hprodSq :
      (Real.sqrt (Real.pi / (x / 2)) * Real.sqrt x) ^ 2 =
        2 * Real.pi := by
    rw [mul_pow, hsquareA, hsquareX]
    field_simp [hx.ne']
  have hprod :
      Real.sqrt (Real.pi / (x / 2)) * Real.sqrt x ≤ 4 := by
    nlinarith
  refine (abs_dfiBesselK0_le hx).trans ?_
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  rw [show 2 / Real.sqrt x * 2 = 4 / Real.sqrt x by ring]
  apply (le_div_iff₀ hsqrtPos).2
  exact hprod


end MathCollab.Density.Stronger.Atkinson
