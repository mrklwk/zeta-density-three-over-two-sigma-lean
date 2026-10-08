module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.LocalDivisorMean

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem summable_weighted_local_integral_norm_zetaSquareNormalizedContribution
    (w : ℝ → ℝ) (hw : Continuous w) (a b : ℝ) :
    Summable (fun n : ℕ =>
      ∫ t in Ioc a b, ‖(w t : ℂ) * zetaSquareNormalizedContribution t n‖) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hw.continuousOn
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (f := fun n : ℕ => max D 0 * ∫ t in Ioc a b, ‖zetaSquareNormalizedContribution t n‖)
  · intro n
    have hInt := ((Complex.continuous_ofReal.comp hw).mul
      (continuous_zetaSquareNormalizedContribution n)).norm.intervalIntegrable (μ := volume) a b
    have hInt' := ((continuous_zetaSquareNormalizedContribution n).norm.intervalIntegrable
      (μ := volume) a b).1.const_mul (max D 0)
    rw [← integral_const_mul]
    apply integral_mono_ae hInt.1 hInt'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right ((hD t ⟨ht.1.le, ht.2⟩).trans
      (le_max_left _ _)) (norm_nonneg _)
  · exact (summable_local_integral_norm_zetaSquareNormalizedContribution a b).mul_left _

theorem hasSum_zetaSquareWeightedLocalMean (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) :
    HasSum (fun n : ℕ => ∫ t in a..b, (w t : ℂ) * zetaSquareNormalizedContribution t n)
      ((∫ t in a..b, w t * zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun n => (((Complex.continuous_ofReal.comp hw).mul
      (continuous_zetaSquareNormalizedContribution n)).intervalIntegrable a b).1)
    (summable_weighted_local_integral_norm_zetaSquareNormalizedContribution w hw a b)
  simp only [Pi.mul_apply, Function.comp_apply] at h
  simp_rw [tsum_mul_left, (hasSum_zetaSquareNormalizedContribution _).tsum_eq,
    ← Complex.ofReal_mul] at h
  simpa only [intervalIntegral.integral_of_le hab, integral_complex_ofReal] using h

def zetaGaussianWeight (T G t : ℝ) : ℝ := Real.exp (-((t - T) / G) ^ 2)

theorem continuous_zetaGaussianWeight (T G : ℝ) : Continuous (zetaGaussianWeight T G) := by
  unfold zetaGaussianWeight
  fun_prop

theorem zetaGaussianWeight_pos (T G t : ℝ) : 0 < zetaGaussianWeight T G t := Real.exp_pos _

theorem zetaGaussianWeight_le_one (T G t : ℝ) : zetaGaussianWeight T G t ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

theorem zetaGaussianWeight_local_lower {T G t : ℝ} (hG : 0 < G)
    (ht : t ∈ Icc (T - G) (T + G)) : 1 ≤ Real.exp 1 * zetaGaussianWeight T G t := by
  have habs : |(t - T) / G| ≤ 1 := by
    rw [abs_div, abs_of_pos hG, div_le_one hG]
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsq : ((t - T) / G) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr habs
  unfold zetaGaussianWeight
  rw [← Real.exp_add]
  exact Real.one_le_exp_iff.mpr (by linarith)

def zetaSquareGaussianWindow (T G L : ℝ) : ℝ :=
  ∫ t in T - G * L..T + G * L, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2

theorem hasSum_zetaSquareGaussianWindow {T G L : ℝ} (hG : 0 < G) (hL : 0 ≤ L) :
    HasSum (fun n : ℕ => ∫ t in T - G * L..T + G * L,
      (zetaGaussianWeight T G t : ℂ) * zetaSquareNormalizedContribution t n)
      (zetaSquareGaussianWindow T G L : ℂ) := by
  exact hasSum_zetaSquareWeightedLocalMean _ (continuous_zetaGaussianWeight T G)
    (by nlinarith)

/-- The averaging constant is `exp 1`, independent of all physical scales. -/
theorem zetaSquareLocalMean_le_gaussian_window {T G L : ℝ}
    (hG : 0 < G) (hL : 1 ≤ L) :
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      Real.exp 1 * zetaSquareGaussianWindow T G L := by
  have hf : Continuous (fun t => zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) :=
    (continuous_zetaGaussianWeight T G).mul (continuous_zetaMomentCriticalNorm.pow 2)
  have hab : T - G ≤ T + G := by linarith
  have hGL : G ≤ G * L := by nlinarith
  calc
    _ ≤ ∫ t in T - G..T + G,
        Real.exp 1 * (zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) := by
      apply intervalIntegral.integral_mono_on hab
        ((continuous_zetaMomentCriticalNorm.pow 2).intervalIntegrable _ _)
        ((hf.const_mul _).intervalIntegrable _ _)
      intro t ht
      have h := mul_le_mul_of_nonneg_right (zetaGaussianWeight_local_lower hG ht)
        (sq_nonneg (zetaMomentCriticalNorm t))
      simpa only [one_mul, mul_assoc, Pi.pow_apply] using h
    _ = Real.exp 1 * ∫ t in T - G..T + G,
        zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact intervalIntegral.integral_mono_interval (by linarith) hab (by linarith)
        (Eventually.of_forall (fun t => mul_nonneg (zetaGaussianWeight_pos T G t).le
          (sq_nonneg _))) (hf.intervalIntegrable _ _)

theorem zetaSquareLocalMean_le_gaussian_divisor_series {T G L : ℝ}
    (hG : 0 < G) (hL : 1 ≤ L) :
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      Real.exp 1 * (∑' n : ℕ, ∫ t in T - G * L..T + G * L,
        (zetaGaussianWeight T G t : ℂ) * zetaSquareNormalizedContribution t n).re := by
  rw [(hasSum_zetaSquareGaussianWindow hG (by linarith)).tsum_eq, Complex.ofReal_re]
  exact zetaSquareLocalMean_le_gaussian_window hG hL

end MathCollab.Density.Stronger.Atkinson
