module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.LeadingDivisor

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


def zetaDivisorWeightNumerator (q w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w * Complex.exp (-q * w)

def zetaDivisorWeightKernel (q w : ℂ) : ℂ := zetaDivisorWeightNumerator q w / w

def zetaDivisorWeight (q : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, zetaDivisorWeightKernel q (1 + (u : ℂ) * I)

def zetaDivisorWeightEnvelope (u : ℝ) : ℝ := Real.exp (-99 * u ^ 2) * (1 + |u|) ^ 8

theorem differentiable_zetaDivisorWeightNumerator (q : ℂ) :
    Differentiable ℂ (zetaDivisorWeightNumerator q) := by
  have haux := differentiable_hughesYoungAuxiliaryZero
  unfold zetaDivisorWeightNumerator
  fun_prop

theorem zetaDivisorWeightNumerator_zero (q : ℂ) : zetaDivisorWeightNumerator q 0 = 1 := by
  simp [zetaDivisorWeightNumerator]

theorem zetaDivisorWeightNumerator_neg (q w : ℂ) :
    zetaDivisorWeightNumerator q (-w) = zetaDivisorWeightNumerator (-q) w := by
  simp [zetaDivisorWeightNumerator, hughesYoungAuxiliaryZero_neg]

theorem zetaDivisorWeightKernel_neg (q w : ℂ) :
    zetaDivisorWeightKernel q (-w) = -zetaDivisorWeightKernel (-q) w := by
  simp only [zetaDivisorWeightKernel, zetaDivisorWeightNumerator_neg, div_neg]

theorem continuous_zetaDivisorWeightKernel_right (q : ℂ) :
    Continuous (fun u : ℝ => zetaDivisorWeightKernel q (1 + (u : ℂ) * I)) := by
  have hw : Continuous (fun u : ℝ => (1 : ℂ) + (u : ℂ) * I) := by fun_prop
  have hne : ∀ u : ℝ, (1 : ℂ) + (u : ℂ) * I ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    norm_num at this
  exact ((differentiable_zetaDivisorWeightNumerator q).continuous.comp hw).div₀ hw hne

theorem integrable_zetaDivisorWeightEnvelope : Integrable zetaDivisorWeightEnvelope := by
  change Integrable (fun u : ℝ => Real.exp (-99 * u ^ 2) * (1 + |u|) ^ 8)
  simpa only [zero_sub, neg_mul] using
    (integrable_exp_sub_mul_sq_mul_add_abs_pow 0 (B := 99) (C := 1) (by norm_num) 8)

theorem norm_zetaDivisorWeightNumerator_right (q : ℂ) (u : ℝ) :
    ‖zetaDivisorWeightNumerator q (1 + (u : ℂ) * I)‖ =
      Real.exp (100 - 100 * u ^ 2 - q.re + q.im * u) *
        ‖hughesYoungAuxiliaryZero (1 + (u : ℂ) * I)‖ := by
  unfold zetaDivisorWeightNumerator
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have he : (100 * ((1 : ℂ) + (u : ℂ) * I) ^ 2).re + (-q * (1 + (u : ℂ) * I)).re =
      100 - 100 * u ^ 2 - q.re + q.im * u := by
    norm_num [pow_two, mul_re, mul_im]
    ring
  calc
    _ = Real.exp ((100 * ((1 : ℂ) + (u : ℂ) * I) ^ 2).re +
        (-q * (1 + (u : ℂ) * I)).re) * ‖hughesYoungAuxiliaryZero (1 + (u : ℂ) * I)‖ := by
      rw [Real.exp_add]
      ring
    _ = _ := by rw [he]

/-- Uniform in the real logarithmic argument; the imaginary argument is
bounded explicitly so both signs of the source phase are covered. -/
theorem norm_zetaDivisorWeightNumerator_right_le {B : ℝ} (hB : 0 ≤ B)
    {q : ℂ} (hq : |q.im| ≤ B) (u : ℝ) :
    ‖zetaDivisorWeightNumerator q (1 + (u : ℂ) * I)‖ ≤
      (625 * Real.exp (100 + B ^ 2 / 2)) * Real.exp (-q.re) * zetaDivisorWeightEnvelope u := by
  have haux := norm_hughesYoungAuxiliaryZero_le_polynomial
    (show 1 ≤ 1 + |u| by linarith [abs_nonneg u])
    (show ‖(1 : ℂ) + (u : ℂ) * I‖ ≤ 1 + |u| by
      simpa [Real.norm_eq_abs] using norm_add_le (1 : ℂ) ((u : ℂ) * I))
  have hqsq : q.im ^ 2 ≤ B ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (add_nonneg hB (abs_nonneg q.im)), sq_abs q.im]
  have he : 100 - 100 * u ^ 2 - q.re + q.im * u ≤
      (100 + B ^ 2 / 2) - q.re - 99 * u ^ 2 := by nlinarith [sq_nonneg (q.im - u)]
  rw [norm_zetaDivisorWeightNumerator_right]
  calc
    _ ≤ Real.exp ((100 + B ^ 2 / 2) - q.re - 99 * u ^ 2) * (625 * (1 + |u|) ^ 8) := by
      exact mul_le_mul (Real.exp_le_exp.mpr he) haux (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      unfold zetaDivisorWeightEnvelope
      rw [show (100 + B ^ 2 / 2) - q.re - 99 * u ^ 2 =
        (100 + B ^ 2 / 2) + (-q.re) + (-99 * u ^ 2) by ring,
        Real.exp_add, Real.exp_add]
      ring

theorem norm_zetaDivisorWeightKernel_right_le {B : ℝ} (hB : 0 ≤ B)
    {q : ℂ} (hq : |q.im| ≤ B) (u : ℝ) :
    ‖zetaDivisorWeightKernel q (1 + (u : ℂ) * I)‖ ≤
      (625 * Real.exp (100 + B ^ 2 / 2)) * Real.exp (-q.re) * zetaDivisorWeightEnvelope u := by
  have hw : 1 ≤ ‖(1 : ℂ) + (u : ℂ) * I‖ := by
    simpa using Complex.abs_re_le_norm ((1 : ℂ) + (u : ℂ) * I)
  rw [zetaDivisorWeightKernel, norm_div]
  calc
    _ ≤ ‖zetaDivisorWeightNumerator q (1 + (u : ℂ) * I)‖ / 1 := by gcongr
    _ ≤ _ := by rw [div_one]; exact norm_zetaDivisorWeightNumerator_right_le hB hq u

theorem integrable_zetaDivisorWeightKernel_right (q : ℂ) :
    Integrable (fun u : ℝ => zetaDivisorWeightKernel q (1 + (u : ℂ) * I)) := by
  apply (integrable_zetaDivisorWeightEnvelope.const_mul
    ((625 * Real.exp (100 + |q.im| ^ 2 / 2)) * Real.exp (-q.re))).mono'
      (continuous_zetaDivisorWeightKernel_right q).aestronglyMeasurable
  filter_upwards with u
  exact norm_zetaDivisorWeightKernel_right_le (abs_nonneg _) le_rfl u

theorem exists_norm_zetaDivisorWeight_le {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℂ, |q.im| ≤ B → ‖zetaDivisorWeight q‖ ≤ C * Real.exp (-q.re) := by
  let M : ℝ := 625 * Real.exp (100 + B ^ 2 / 2)
  let J : ℝ := ∫ u : ℝ, zetaDivisorWeightEnvelope u
  have hJ : 0 ≤ J := integral_nonneg (by intro u; unfold zetaDivisorWeightEnvelope; positivity)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨1 + M * J / (2 * Real.pi), by positivity, ?_⟩
  intro q hq
  have h := integral_mono (integrable_zetaDivisorWeightKernel_right q).norm
    (integrable_zetaDivisorWeightEnvelope.const_mul (M * Real.exp (-q.re)))
    (norm_zetaDivisorWeightKernel_right_le hB hq)
  rw [integral_const_mul] at h
  unfold zetaDivisorWeight
  rw [norm_mul]
  have hp : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hp]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans
  calc
    _ = (M * J / (2 * Real.pi)) * Real.exp (-q.re) := by dsimp [J]; ring
    _ ≤ _ := by nlinarith [Real.exp_pos (-q.re)]

end MathCollab.Density.Stronger.Atkinson
