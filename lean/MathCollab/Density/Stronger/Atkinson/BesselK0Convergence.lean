module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselMellin.lean,
exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/BESSEL_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain
Apache-2.0 attribution. No Estermann or general-modulus source closure is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselMellinBeta

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open scoped Topology Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem integrableOn_cpow_mul_exp_neg_mul_Ioi
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x)))
      (Set.Ioi 0) := by
  let f : ℝ → ℂ := fun u => Complex.exp (-(u : ℂ))
  have hbase : MellinConvergent f s := by
    unfold MellinConvergent f
    refine (Complex.GammaIntegral_convergent hs).congr_fun ?_ measurableSet_Ioi
    intro x hx
    change ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ))
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hscaled : MellinConvergent (fun x => f (a * x)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) ha).2 hbase
  unfold MellinConvergent at hscaled
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [f, smul_eq_mul, Complex.ofReal_mul]

/-- Norm of the two-variable Gamma kernel on the positive quadrant. -/
theorem norm_cpow_mul_exp_neg_cosh
    {s : ℂ} {x t : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (s - 1) * Complex.exp (-(x * Real.cosh t))‖ =
      x ^ (s.re - 1) * Real.exp (-(Real.cosh t * x)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  simp only [sub_re, one_re, neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring_nf

/-- Exact integral of the norm in the radial variable. -/
theorem integral_norm_cpow_mul_exp_neg_cosh_Ioi
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    (∫ x : ℝ in Set.Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * Complex.exp (-(x * Real.cosh t))‖) =
      (1 / Real.cosh t) ^ s.re * Real.Gamma s.re := by
  calc
    (∫ x : ℝ in Set.Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * Complex.exp (-(x * Real.cosh t))‖) =
        ∫ x : ℝ in Set.Ioi 0,
          x ^ (s.re - 1) * Real.exp (-(Real.cosh t * x)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact norm_cpow_mul_exp_neg_cosh hx
    _ = (1 / Real.cosh t) ^ s.re * Real.Gamma s.re :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos t)

/-- The real reciprocal-cosh power inherited from the beta integral is
integrable. -/
theorem integrableOn_inv_cosh_rpow_Ioi
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (1 / Real.cosh t) ^ r) (Set.Ioi 0) := by
  have hcomplex := integrableOn_cosh_cpow_neg_two_mul_Ioi
    (w := ((r / 2 : ℝ) : ℂ)) (by simp [hr])
  have hnorm : IntegrableOn
      (fun t : ℝ => ‖(Real.cosh t : ℂ) ^ (-2 * ((r / 2 : ℝ) : ℂ))‖)
      (Set.Ioi 0) := hcomplex.norm
  refine hnorm.congr_fun ?_ measurableSet_Ioi
  intro t _
  change ‖(Real.cosh t : ℂ) ^ (-2 * ((r / 2 : ℝ) : ℂ))‖ =
    (1 / Real.cosh t) ^ r
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.cosh_pos t)]
  have hre : (-2 * ((r / 2 : ℝ) : ℂ)).re = -r := by
    norm_num
    ring
  rw [hre]
  rw [Real.rpow_neg (Real.cosh_pos t).le, one_div]
  exact (Real.inv_rpow (x := Real.cosh t) (Real.cosh_pos t).le r).symm

/-- Joint absolute integrability needed to exchange the two integrals in
the Mellin transform of `K₀`. -/
theorem integrableOn_dfiBesselK0_mellin_joint
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (p.1 : ℂ) ^ (s - 1) *
          Complex.exp (-(p.1 * Real.cosh p.2)))
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Complex.exp (-(p.1 * Real.cosh p.2))
  have hcont : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have hreal : ContinuousAt
          (fun x : ℝ => (x : ℂ) ^ (s - 1)) p.1 :=
        (continuousAt_cpow_const
          (Complex.ofReal_mem_slitPlane.2 hp.1)).comp
            Complex.continuous_ofReal.continuousAt
      exact hreal.comp continuousAt_fst
    · fun_prop
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hprod : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · filter_upwards with t
      change IntegrableOn (fun x : ℝ => F (x, t)) (Set.Ioi 0)
      refine (integrableOn_cpow_mul_exp_neg_mul_Ioi hs
        (Real.cosh_pos t)).congr_fun ?_ measurableSet_Ioi
      intro x _
      dsimp [F]
      congr 2
      push_cast
      ring
    · have hout : IntegrableOn
          (fun t : ℝ =>
            (1 / Real.cosh t) ^ s.re * Real.Gamma s.re) (Set.Ioi 0) :=
        (integrableOn_inv_cosh_rpow_Ioi hs).mul_const _
      refine hout.congr_fun ?_ measurableSet_Ioi
      intro t _
      exact (integral_norm_cpow_mul_exp_neg_cosh_Ioi hs t).symm
  simpa only [F, Measure.prod_restrict] using! hprod

/-- Reciprocal-cosh version of the hyperbolic beta evaluation. -/
theorem integral_inv_cosh_cpow_Ioi_eq
    {s : ℂ} :
    (∫ t : ℝ in Set.Ioi 0,
        ((1 / Real.cosh t : ℝ) : ℂ) ^ s) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2) := by
  calc
    (∫ t : ℝ in Set.Ioi 0,
        ((1 / Real.cosh t : ℝ) : ℂ) ^ s) =
        ∫ t : ℝ in Set.Ioi 0,
          (Real.cosh t : ℂ) ^ (-2 * (s / 2)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t _
            change ((1 / Real.cosh t : ℝ) : ℂ) ^ s =
              (Real.cosh t : ℂ) ^ (-2 * (s / 2))
            rw [show -2 * (s / 2) = -s by ring, Complex.cpow_neg]
            rw [Complex.ofReal_div, Complex.ofReal_one, one_div,
              Complex.inv_cpow]
            rw [Complex.arg_ofReal_of_nonneg (Real.cosh_pos t).le]
            exact Real.pi_ne_zero.symm
    _ = (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2) :=
      integral_cosh_cpow_neg_two_mul_Ioi_eq (s / 2)

/-- Complex realization of the defining integral for `K₀`. -/
theorem dfiBesselK0_ofReal_eq_integral {x : ℝ} :
    (dfiBesselK0 x : ℂ) =
      ∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-(x * Real.cosh t)) := by
  unfold dfiBesselK0
  refine integral_ofReal.symm.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change (Real.exp (-x * Real.cosh t) : ℂ) =
    Complex.exp (-(x * Real.cosh t))
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Absolute Mellin convergence of the literal Macdonald kernel throughout
its natural right half-plane.  This is extracted from the joint integral
used in the Fubini evaluation, so it records convergence independently of
the later closed-form calculation. -/
theorem mellinConvergent_dfiBesselK0
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => (dfiBesselK0 x : ℂ)) s := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Complex.exp (-(p.1 * Real.cosh p.2))
  have hjointOn : IntegrableOn F (Set.Ioi 0 ×ˢ Set.Ioi 0) :=
    integrableOn_dfiBesselK0_mellin_joint hs
  have hjoint : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    simpa only [F, Measure.prod_restrict] using! hjointOn
  have hIntegrated : IntegrableOn
      (fun x : ℝ => ∫ t : ℝ in Set.Ioi 0, F (x, t))
      (Set.Ioi 0) := hjoint.integral_prod_left
  unfold MellinConvergent
  refine hIntegrated.congr_fun ?_ measurableSet_Ioi
  intro x _hx
  change (∫ t : ℝ in Set.Ioi 0, F (x, t)) =
    (x : ℂ) ^ (s - 1) • (dfiBesselK0 x : ℂ)
  rw [dfiBesselK0_ofReal_eq_integral]
  simp only [smul_eq_mul]
  rw [
    ← MeasureTheory.integral_const_mul]

/-- Mellin convergence after the square-root dilation appearing in DFI's
literal `K₀(4π√(nx)/q)` transform. -/
theorem mellinConvergent_dfiBesselK0_mul_sqrt
    {A : ℝ} (hA : 0 < A) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent
      (fun x : ℝ => (dfiBesselK0 (A * Real.sqrt x) : ℂ)) s := by
  have hbase : MellinConvergent
      (fun y : ℝ => (dfiBesselK0 y : ℂ)) (2 * s) := by
    apply mellinConvergent_dfiBesselK0
    norm_num
    linarith
  have hscaled : MellinConvergent
      (fun y : ℝ => (dfiBesselK0 (A * y) : ℂ)) (2 * s) :=
    (MellinConvergent.comp_mul_left hA).2 hbase
  have hscaled' : MellinConvergent
      (fun y : ℝ => (dfiBesselK0 (A * y) : ℂ))
        (s / ((1 / 2 : ℝ) : ℂ)) := by
    convert hscaled using 1
    norm_num
    ring
  have hroot := (MellinConvergent.comp_rpow
    (f := fun y : ℝ => (dfiBesselK0 (A * y) : ℂ))
    (s := s) (a := (1 / 2 : ℝ)) (by norm_num)).2
      hscaled'
  simpa only [Real.sqrt_eq_rpow] using hroot


end MathCollab.Density.Stronger.Atkinson
