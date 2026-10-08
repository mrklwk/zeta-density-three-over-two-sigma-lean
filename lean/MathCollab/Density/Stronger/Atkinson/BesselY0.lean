module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselKernel.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- The exponentially decaying term in Schläfli's real integral
representation of the order-zero Neumann kernel. -/
noncomputable def dfiBesselY0Tail (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)

/-- The oscillatory term in Schläfli's representation, written after the
change of variables `u = π/2 - θ`.  Taking the imaginary part packages the
real sine integral while retaining the complex exponential needed for the
first-derivative estimate. -/
noncomputable def dfiBesselY0Osc (x : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..Real.pi / 2,
    Complex.exp (Complex.I * (x * Real.cos u))).im

/-- DFI's order-zero Neumann kernel, defined by the DLMF/Schläfli integral
representation
`Y₀(x) = (2/π) ( ∫₀^π/² sin(x cos u) du
                         - ∫₀^∞ exp(-xt)/sqrt(1+t²) dt )`.
The representation is used only for positive arguments, exactly as in DFI
Proposition 1. -/
noncomputable def dfiBesselY0 (x : ℝ) : ℝ :=
  (2 / Real.pi) * (dfiBesselY0Osc x - dfiBesselY0Tail x)


theorem integrableOn_dfiBesselY0Tail_integrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-x * t) / Real.sqrt (1 + t ^ 2))
      (Set.Ioi 0) := by
  have hExp : IntegrableOn (fun t : ℝ => t ^ (0 : ℝ) *
      Real.exp (-x * t ^ (1 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hx
  have hExp' : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Set.Ioi 0) := by
    convert hExp using 1
    ext t
    simp
  refine hExp'.mono' ?_ ?_
  · have hcont : ContinuousOn
        (fun t : ℝ => Real.exp (-x * t) / Real.sqrt (1 + t ^ 2))
        (Set.Ioi 0) := by
      exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousOn.div
          (Real.continuous_sqrt.comp
            (continuous_const.add (continuous_id.pow 2))).continuousOn
          (fun t ht => ne_of_gt (Real.sqrt_pos.2 (by positivity)))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _)]
    have hsqrt : 1 ≤ Real.sqrt (1 + t ^ 2) := by
      have harg : 0 ≤ 1 + t ^ 2 := by positivity
      have hsquare := Real.sq_sqrt harg
      have hnonneg := Real.sqrt_nonneg (1 + t ^ 2)
      nlinarith [sq_nonneg t]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self (Real.exp_pos _).le hsqrt


/-- The literal finite oscillatory integral is integrable at every real argument. -/
theorem intervalIntegrable_dfiBesselY0Osc_integrand (x : ℝ) :
    IntervalIntegrable (fun u : ℝ => Complex.exp (Complex.I * (x * Real.cos u)))
      volume 0 (Real.pi / 2) := by
  apply Continuous.intervalIntegrable
  fun_prop

end MathCollab.Density.Stronger.Atkinson
