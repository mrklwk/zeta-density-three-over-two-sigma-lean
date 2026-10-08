module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

structure IntervalC2Bound (f : ℝ → ℂ) (a b M R : ℝ) : Prop where
  nonneg : 0 ≤ M
  scale_nonneg : 0 ≤ R
  smooth : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 f x
  norm_le : ∀ x ∈ Icc a b, ‖f x‖ ≤ M
  deriv_le : ∀ x ∈ Icc a b, ‖deriv f x‖ ≤ M * R
  second_le : ∀ x ∈ Icc a b, ‖iteratedDeriv 2 f x‖ ≤ M * R ^ 2

theorem intervalC2Bound_const (c : ℂ) (a b : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalC2Bound (fun _ : ℝ => c) a b ‖c‖ R := by
  refine ⟨norm_nonneg _, hR, fun _ _ => contDiffAt_const, fun _ _ => le_rfl, ?_, ?_⟩
  · intro x hx
    simp only [deriv_const, norm_zero]
    exact mul_nonneg (norm_nonneg _) hR
  · intro x hx
    simp only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 by norm_num, ite_false, norm_zero]
    positivity

theorem IntervalC2Bound.mono {f : ℝ → ℂ} {a b M N R S : ℝ}
    (hf : IntervalC2Bound f a b M R) (hMN : M ≤ N) (hRS : R ≤ S) :
    IntervalC2Bound f a b N S := by
  have hN : 0 ≤ N := hf.nonneg.trans hMN
  refine ⟨hN, hf.scale_nonneg.trans hRS, hf.smooth,
    fun x hx => (hf.norm_le x hx).trans hMN, ?_, ?_⟩
  · intro x hx
    exact (hf.deriv_le x hx).trans (mul_le_mul hMN hRS hf.scale_nonneg hN)
  · intro x hx
    exact (hf.second_le x hx).trans
      (mul_le_mul hMN (pow_le_pow_left₀ hf.scale_nonneg hRS 2) (sq_nonneg _) hN)

theorem iteratedDeriv_two_mul {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun y => f y * g y) x =
      f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x + iteratedDeriv 2 f x * g x := by
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] using
    iteratedDeriv_fun_mul hf hg

theorem IntervalC2Bound.mul {f g : ℝ → ℂ} {a b M N R : ℝ}
    (hf : IntervalC2Bound f a b M R) (hg : IntervalC2Bound g a b N R) :
    IntervalC2Bound (fun x => f x * g x) a b (4 * M * N) R := by
  have hMN : 0 ≤ M * N := mul_nonneg hf.nonneg hg.nonneg
  have hMR : 0 ≤ M * R := mul_nonneg hf.nonneg hf.scale_nonneg
  have hNR : 0 ≤ N * R := mul_nonneg hg.nonneg hf.scale_nonneg
  refine ⟨by nlinarith, hf.scale_nonneg, fun x hx => (hf.smooth x hx).mul (hg.smooth x hx),
    ?_, ?_, ?_⟩
  · intro x hx
    rw [norm_mul]
    exact (mul_le_mul (hf.norm_le x hx) (hg.norm_le x hx) (norm_nonneg _) hf.nonneg).trans
      (by nlinarith)
  · intro x hx
    rw [deriv_fun_mul ((hf.smooth x hx).differentiableAt (by norm_num))
      ((hg.smooth x hx).differentiableAt (by norm_num))]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (M * R) * N + M * (N * R) :=
        add_le_add (mul_le_mul (hf.deriv_le x hx) (hg.norm_le x hx) (norm_nonneg _) hMR)
          (mul_le_mul (hf.norm_le x hx) (hg.deriv_le x hx) (norm_nonneg _) hf.nonneg)
      _ ≤ _ := by nlinarith [mul_nonneg hMN hf.scale_nonneg]
  · intro x hx
    rw [iteratedDeriv_two_mul (hf.smooth x hx) (hg.smooth x hx)]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul, norm_ofNat]
    calc
      _ ≤ M * (N * R ^ 2) + 2 * (M * R) * (N * R) + (M * R ^ 2) * N := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul (hf.norm_le x hx) (hg.second_le x hx) (norm_nonneg _) hf.nonneg
          · exact mul_le_mul
              (mul_le_mul_of_nonneg_left (hf.deriv_le x hx) (by norm_num))
              (hg.deriv_le x hx) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hf.second_le x hx) (hg.norm_le x hx) (norm_nonneg _)
            (mul_nonneg hf.nonneg (sq_nonneg _))
      _ = _ := by ring

theorem exists_intervalC2Bound_fixed {f : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 f x) :
    ∃ M : ℝ, 0 < M ∧ IntervalC2Bound f a b M 1 := by
  have h0 : ContinuousOn f (Icc a b) := fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt
  have h1 : ContinuousOn (deriv f) (Icc a b) := fun x hx =>
    ((hf x hx).derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have h2 : ContinuousOn (iteratedDeriv 2 f) (Icc a b) := by
    intro x hx
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (((hf x hx).derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn h0
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn h1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h2
  let M : ℝ := 1 + |A| + |B| + |C|
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : A ≤ M := by dsimp [M]; linarith [le_abs_self A, abs_nonneg B, abs_nonneg C]
  have hBM : B ≤ M := by dsimp [M]; linarith [le_abs_self B, abs_nonneg A, abs_nonneg C]
  have hCM : C ≤ M := by dsimp [M]; linarith [le_abs_self C, abs_nonneg A, abs_nonneg B]
  refine ⟨M, hM, hM.le, by norm_num, hf, fun x hx => (hA x hx).trans hAM, ?_, ?_⟩
  · intro x hx
    simpa only [mul_one] using (hB x hx).trans hBM
  · intro x hx
    simpa only [one_pow, mul_one] using (hC x hx).trans hCM

theorem IntervalC2Bound.norm_sub_le {f : ℝ → ℂ} {a b M R x y : ℝ}
    (hf : IntervalC2Bound f a b M R) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f y - f x‖ ≤ M * R * |y - x| := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf.smooth z hz).differentiableAt (by norm_num)) hf.deriv_le hx hy
  simpa only [Real.norm_eq_abs] using h

end MathCollab.Density.Stronger.Atkinson
