module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIY0Abel.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselComplexLaplace

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Abel-regularized oscillatory Mellin integrals for `Y₀`

These are the one-dimensional Gamma integrals used when the oscillatory
Schläfli term is damped by `exp (-εx)`.  All integrals in this file are
absolutely convergent; the undamped Neumann transform will be recovered by
a dominated Abel limit.
-/

open Complex Set MeasureTheory Filter
open scoped Topology Interval

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem integral_cpow_mul_damped_cexp_Ioi
    {s : ℂ} (hs : 0 < s.re) {ε a : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) *
          cexp (-((ε : ℂ) * x)) * cexp (I * (a * x))) =
      ((ε : ℂ) - I * a) ^ (-s) * Gamma s := by
  have haRe : 0 < ((ε : ℂ) - I * a).re := by simp [hε]
  have h := dfiComplexLaplace_eq hs haRe
  unfold dfiComplexLaplace at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (I * ((a : ℂ) * x)) =
    (x : ℂ) ^ (s - 1) * cexp (-(((ε : ℂ) - I * a) * x))
  rw [show (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (I * ((a : ℂ) * x)) =
    (x : ℂ) ^ (s - 1) *
      (cexp (-((ε : ℂ) * x)) * cexp (I * ((a : ℂ) * x))) by ring,
    ← Complex.exp_add]
  congr 2
  ring

theorem integral_cpow_mul_damped_cexp_neg_Ioi
    {s : ℂ} (hs : 0 < s.re) {ε a : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) *
          cexp (-((ε : ℂ) * x)) * cexp (-(I * (a * x)))) =
      ((ε : ℂ) + I * a) ^ (-s) * Gamma s := by
  have haRe : 0 < ((ε : ℂ) + I * a).re := by simp [hε]
  have h := dfiComplexLaplace_eq hs haRe
  unfold dfiComplexLaplace at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (-(I * ((a : ℂ) * x))) =
    (x : ℂ) ^ (s - 1) * cexp (-(((ε : ℂ) + I * a) * x))
  rw [show (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (-(I * ((a : ℂ) * x))) =
    (x : ℂ) ^ (s - 1) *
      (cexp (-((ε : ℂ) * x)) * cexp (-(I * ((a : ℂ) * x)))) by ring,
    ← Complex.exp_add]
  congr 2
  ring

theorem integral_cpow_mul_damped_sin_Ioi
    {s : ℂ} (hs : 0 < s.re) {ε a : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) * Real.sin (a * x)) =
      (((ε : ℂ) - I * a) ^ (-s) - ((ε : ℂ) + I * a) ^ (-s)) /
        (2 * I) * Gamma s := by
  have hp := integral_cpow_mul_damped_cexp_Ioi hs hε (a := a)
  have hm := integral_cpow_mul_damped_cexp_neg_Ioi hs hε (a := a)
  let P : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) *
    cexp (-((ε : ℂ) * x)) * cexp (I * ((a : ℂ) * x))
  let M : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) *
    cexp (-((ε : ℂ) * x)) * cexp (-(I * ((a : ℂ) * x)))
  have hPInt : IntegrableOn P (Set.Ioi 0) := by
    have h := integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hs
      (show 0 < ((ε : ℂ) - I * a).re by simp [hε])
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    dsimp [P]
    rw [show -(((ε : ℂ) - I * a) * x) =
      -((ε : ℂ) * x) + I * ((a : ℂ) * x) by ring, Complex.exp_add]
    ring
  have hMInt : IntegrableOn M (Set.Ioi 0) := by
    have h := integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hs
      (show 0 < ((ε : ℂ) + I * a).re by simp [hε])
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    dsimp [M]
    rw [show -(((ε : ℂ) + I * a) * x) =
      -((ε : ℂ) * x) + -(I * ((a : ℂ) * x)) by ring, Complex.exp_add]
    ring
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) * Real.sin (a * x)) =
      ∫ x : ℝ in Set.Ioi 0, (P x - M x) / (2 * I) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp [P, M]
      have hExp : ((Real.exp (-ε * x) : ℝ) : ℂ) =
          cexp (-((ε : ℂ) * x)) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [show (Real.sin (a * x) : ℂ) =
          (cexp (I * (a * x)) - cexp (-(I * (a * x)))) / (2 * I) by
        have hSin (y : ℝ) : (Real.sin y : ℂ) =
            (cexp (I * y) - cexp (-(I * y))) / (2 * I) := by
          rw [show I * (y : ℂ) = (y : ℂ) * I by ring,
            show -((y : ℂ) * I) = ((-y : ℝ) : ℂ) * I by push_cast; ring,
            Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg,
            Complex.cos_neg, Complex.sin_neg,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin]
          push_cast
          field_simp
          ring
        simpa only [Complex.ofReal_mul] using hSin (a * x)]
      rw [hExp]
      ring
    _ = (∫ x : ℝ in Set.Ioi 0, P x - M x) / (2 * I) := by
      rw [MeasureTheory.integral_div]
    _ = ((∫ x : ℝ in Set.Ioi 0, P x) -
        ∫ x : ℝ in Set.Ioi 0, M x) / (2 * I) := by
      rw [MeasureTheory.integral_sub hPInt hMInt]
    _ = (((ε : ℂ) - I * a) ^ (-s) - ((ε : ℂ) + I * a) ^ (-s)) /
        (2 * I) * Gamma s := by
      rw [show (∫ x : ℝ in Set.Ioi 0, P x) =
          ((ε : ℂ) - I * a) ^ (-s) * Gamma s by exact hp,
        show (∫ x : ℝ in Set.Ioi 0, M x) =
          ((ε : ℂ) + I * a) ^ (-s) * Gamma s by exact hm]
      field_simp

/-- The two damped complex powers have their expected nontangential Abel
limit at the imaginary axis. -/
theorem tendsto_dfiDampedSineFactor
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ =>
        (((ε : ℂ) - I * a) ^ (-s) - ((ε : ℂ) + I * a) ^ (-s)) / (2 * I))
      (𝓝[>] 0)
      (𝓝 (((-I * a) ^ (-s) - (I * a) ^ (-s)) / (2 * I))) := by
  have hnegSlit : -I * (a : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [ha.ne']
  have hposSlit : I * (a : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [ha.ne']
  have hnegBase : Tendsto (fun ε : ℝ => (ε : ℂ) - I * a) (𝓝 0)
      (𝓝 (-I * a)) := by
    simpa using! ((Complex.continuous_ofReal.sub continuous_const).tendsto 0)
  have hposBase : Tendsto (fun ε : ℝ => (ε : ℂ) + I * a) (𝓝 0)
      (𝓝 (I * a)) := by
    simpa using! ((Complex.continuous_ofReal.add continuous_const).tendsto 0)
  have hneg : Tendsto (fun ε : ℝ => ((ε : ℂ) - I * a) ^ (-s)) (𝓝[>] 0)
      (𝓝 ((-I * a) ^ (-s))) :=
    ((continuousAt_cpow_const hnegSlit).tendsto.comp hnegBase).mono_left inf_le_left
  have hpos : Tendsto (fun ε : ℝ => ((ε : ℂ) + I * a) ^ (-s)) (𝓝[>] 0)
      (𝓝 ((I * a) ^ (-s))) :=
    ((continuousAt_cpow_const hposSlit).tendsto.comp hposBase).mono_left inf_le_left
  exact (hneg.sub hpos).div_const (2 * I)

/-- The boundary value of the damped sine factor.  This is the exact
oscillatory Mellin factor used in the Schläfli representation of `Y₀`. -/
theorem dfiDampedSineFactor_limit_eq
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (((-I * a) ^ (-s) - (I * a) ^ (-s)) / (2 * I)) =
      (a : ℂ) ^ (-s) * Complex.sin (Real.pi * s / 2) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hnegI : (-I : ℂ) ≠ 0 := by simp
  have hI : (I : ℂ) ≠ 0 := by simp
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hnegI haC),
    Complex.cpow_def_of_ne_zero (mul_ne_zero hI haC),
    Complex.cpow_def_of_ne_zero haC,
    Complex.log_mul_ofReal a ha (-I) hnegI,
    Complex.log_mul_ofReal a ha I hI,
    Complex.log_neg_I, Complex.log_I]
  rw [show (Real.log a + -(Real.pi / 2) * I) * -s =
      Real.log a * -s + I * (Real.pi * s / 2) by ring,
    show (Real.log a + Real.pi / 2 * I) * -s =
      Real.log a * -s + -(I * (Real.pi * s / 2)) by ring,
    Complex.exp_add, Complex.exp_add]
  simp only [Complex.sin]
  rw [Complex.ofReal_log ha.le]
  have hp : cexp (I * (Real.pi * s / 2)) =
      cexp (Real.pi * s / 2 * I) := by
    apply congrArg cexp
    ring
  have hm : cexp (-(I * (Real.pi * s / 2))) =
      cexp (-(Real.pi * s / 2) * I) := by
    apply congrArg cexp
    ring
  rw [hp, hm]
  field_simp
  have hIsq : I ^ 2 = (-1 : ℂ) := by rw [pow_two, Complex.I_mul_I]
  rw [hIsq]
  ring

end MathCollab.Density.Stronger.Atkinson
