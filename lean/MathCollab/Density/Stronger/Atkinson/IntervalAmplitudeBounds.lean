module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import Mathlib

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete C1 amplitude bounds on an interval

The bound records the actual supremum and integral of the norm of
the derivative. Product rules preserve those literal analytic quantities;
the source application below must construct every bound it consumes.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

structure IntervalC1Bound (f : ℝ → ℂ) (a b M : ℝ) : Prop where
  nonneg : 0 ≤ M
  smooth : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x
  norm_le : ∀ x ∈ Icc a b, ‖f x‖ ≤ M
  variation_le : (∫ x in a..b, ‖deriv f x‖) ≤ M

theorem IntervalC1Bound.derivative_integrable {f : ℝ → ℂ} {a b M : ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) :
    IntervalIntegrable (deriv f) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  exact ((hf.smooth x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

theorem IntervalC1Bound.mono {f : ℝ → ℂ} {a b M N : ℝ}
    (hf : IntervalC1Bound f a b M) (hMN : M ≤ N) : IntervalC1Bound f a b N :=
  ⟨hf.nonneg.trans hMN, hf.smooth, fun x hx => (hf.norm_le x hx).trans hMN,
    hf.variation_le.trans hMN⟩

theorem intervalC1Bound_const (c : ℂ) (a b : ℝ) :
    IntervalC1Bound (fun _ : ℝ => c) a b ‖c‖ := by
  refine ⟨norm_nonneg _, fun _ _ => contDiffAt_const, fun _ _ => le_rfl, ?_⟩
  simp only [deriv_const, norm_zero, intervalIntegral.integral_zero, norm_nonneg]

theorem IntervalC1Bound.mul {f g : ℝ → ℂ} {a b M N : ℝ}
    (hf : IntervalC1Bound f a b M) (hg : IntervalC1Bound g a b N) (hab : a ≤ b) :
    IntervalC1Bound (fun x => f x * g x) a b (2 * M * N) := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x :=
    ((hf.smooth x hx).differentiableAt (by norm_num)).hasDerivAt.mul
      ((hg.smooth x hx).differentiableAt (by norm_num)).hasDerivAt |>.deriv
  have hs : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 (fun y => f y * g y) x :=
    fun x hx => (hf.smooth x hx).mul (hg.smooth x hx)
  have hdi : IntervalIntegrable (deriv (fun x => f x * g x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact ((hs x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨by positivity [hf.nonneg, hg.nonneg], hs, ?_, ?_⟩
  · intro x hx
    rw [norm_mul]
    have h := mul_le_mul (hf.norm_le x hx) (hg.norm_le x hx) (norm_nonneg _) hf.nonneg
    nlinarith [mul_nonneg hf.nonneg hg.nonneg]
  · calc
      _ ≤ ∫ x in a..b, ‖deriv f x‖ * N + M * ‖deriv g x‖ := by
        apply intervalIntegral.integral_mono_on hab hdi.norm
          (((hf.derivative_integrable hab).norm.mul_const N).add
            ((hg.derivative_integrable hab).norm.const_mul M))
        intro x hx
        rw [hd x hx]
        apply (norm_add_le _ _).trans
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hg.norm_le x hx) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hf.norm_le x hx) (norm_nonneg _))
      _ = (∫ x in a..b, ‖deriv f x‖) * N + M * (∫ x in a..b, ‖deriv g x‖) := by
        rw [intervalIntegral.integral_add ((hf.derivative_integrable hab).norm.mul_const N)
          ((hg.derivative_integrable hab).norm.const_mul M),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
      _ ≤ M * N + M * N := add_le_add
        (mul_le_mul_of_nonneg_right hf.variation_le hg.nonneg)
        (mul_le_mul_of_nonneg_left hg.variation_le hf.nonneg)
      _ = _ := by ring

theorem intervalC1Bound_ofReal_of_deriv_nonneg {f : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hbound : ∀ x ∈ Icc a b, 0 ≤ f x ∧ f x ≤ M)
    (hd : ∀ x ∈ Icc a b, 0 ≤ deriv f x) :
    IntervalC1Bound (fun x => (f x : ℂ)) a b M := by
  have hfd (x : ℝ) (hx : x ∈ Icc a b) :=
    ((hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hcast (x : ℝ) (hx : x ∈ Icc a b) :
      deriv (fun y => (f y : ℂ)) x = ((deriv f x : ℝ) : ℂ) := (hfd x hx).ofReal_comp.deriv
  have hfi : IntervalIntegrable (deriv f) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact ((hf x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨hM, fun x hx => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hf x hx), ?_, ?_⟩
  · intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1]
    exact (hbound x hx).2
  · have heq : (∫ x in a..b, ‖deriv (fun y => (f y : ℂ)) x‖) =
        ∫ x in a..b, deriv f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      change ‖deriv (fun y : ℝ => (f y : ℂ)) x‖ = deriv f x
      rw [hcast x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd x hx)]
    rw [heq]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact hfd x hx) hfi]
    linarith [(hbound a ⟨le_rfl, hab⟩).1, (hbound b ⟨hab, le_rfl⟩).2]

theorem intervalC1Bound_ofReal_of_deriv_nonpos {f : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hbound : ∀ x ∈ Icc a b, 0 ≤ f x ∧ f x ≤ M)
    (hd : ∀ x ∈ Icc a b, deriv f x ≤ 0) :
    IntervalC1Bound (fun x => (f x : ℂ)) a b M := by
  have hfd (x : ℝ) (hx : x ∈ Icc a b) :=
    ((hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hcast (x : ℝ) (hx : x ∈ Icc a b) :
      deriv (fun y => (f y : ℂ)) x = ((deriv f x : ℝ) : ℂ) := (hfd x hx).ofReal_comp.deriv
  have hfi : IntervalIntegrable (deriv f) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact ((hf x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨hM, fun x hx => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hf x hx), ?_, ?_⟩
  · intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1]
    exact (hbound x hx).2
  · have heq : (∫ x in a..b, ‖deriv (fun y => (f y : ℂ)) x‖) =
        ∫ x in a..b, -deriv f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      change ‖deriv (fun y : ℝ => (f y : ℂ)) x‖ = -deriv f x
      rw [hcast x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hd x hx)]
    rw [heq]
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
        rw [uIcc_of_le hab] at hx
        exact hfd x hx) hfi]
    linarith [(hbound b ⟨hab, le_rfl⟩).1, (hbound a ⟨le_rfl, hab⟩).2]


theorem IntervalC1Bound.join {f : ℝ → ℂ} {a b c M N : ℝ}
    (hf : IntervalC1Bound f a b M) (hg : IntervalC1Bound f b c N)
    (hab : a ≤ b) (hbc : b ≤ c) : IntervalC1Bound f a c (M + N) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxb : x ≤ b
    · exact hf.smooth x ⟨hx.1, hxb⟩
    · exact hg.smooth x ⟨(lt_of_not_ge hxb).le, hx.2⟩
  · intro x hx
    by_cases hxb : x ≤ b
    · exact (hf.norm_le x ⟨hx.1, hxb⟩).trans (le_add_of_nonneg_right hg.nonneg)
    · exact (hg.norm_le x ⟨(lt_of_not_ge hxb).le, hx.2⟩).trans (le_add_of_nonneg_left hf.nonneg)
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.derivative_integrable hab).norm (hg.derivative_integrable hbc).norm]
    exact add_le_add hf.variation_le hg.variation_le


end MathCollab.Density.Stronger.Atkinson
