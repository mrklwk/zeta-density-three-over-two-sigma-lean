module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.GaussianPolynomial
public import MathCollab.Density.Stronger.Fourth.SquareDivisorSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem continuous_zetaSquareRightKernel_height (u : ℝ) :
    Continuous (fun t : ℝ => zetaSquareRightKernel t u) := by
  have hGamma : Continuous (fun t : ℝ =>
      Gammaℝ (afeCriticalPoint t + (1 + (u : ℂ) * I))) := by
    convert continuous_GammaR_afe_vertical u (c := 1) (by norm_num) using 1
    funext t
    congr 1
    dsimp [afeCriticalPoint]
    ring
  have hden : Continuous zetaSquarePoleNormalization := by
    unfold zetaSquarePoleNormalization afeCriticalPoint
    fun_prop
  unfold zetaSquareRightKernel
  dsimp only
  apply Continuous.div_const
  apply Continuous.div ?_ hden zetaSquarePoleNormalization_ne_zero
  unfold afeCriticalPoint at *
  fun_prop (disch := assumption)

theorem continuous_zetaSquareDivisorTerm_height (n : ℕ) (u : ℝ) :
    Continuous (fun t : ℝ => zetaSquareDivisorTerm t n u) := by
  have hterm : Continuous (fun t : ℝ =>
      divisorDirichletTerm (afeCriticalPoint t + (1 + (u : ℂ) * I)) n) := by
    convert continuous_divisorDirichletTerm_vertical u 1 n using 1
    funext t
    congr 1
    dsimp [afeCriticalPoint]
    ring
  exact hterm.mul (continuous_zetaSquareRightKernel_height u)

theorem exists_zetaSquareRightKernel_compact_majorant (M : ℝ) :
    ∃ B : ℝ → ℝ, Integrable B ∧ (∀ u, 0 ≤ B u) ∧
      ∀ t : ℝ, |t| ≤ M → ∀ u : ℝ, ‖zetaSquareRightKernel t u‖ ≤ B u := by
  obtain ⟨C, hC, hbound⟩ := exists_zetaSquareRightKernel_uniform_gaussian_bound
  refine ⟨fun u => C * (Real.exp (100 - 100 * u ^ 2) * (3 + M + |u|) ^ 12),
    (integrable_exp_sub_mul_sq_mul_add_abs_pow (C := 3 + M) 100
      (by norm_num : (0 : ℝ) < 100) 12).const_mul C, ?_, ?_⟩
  · intro u
    positivity
  · intro t ht u
    apply (hbound t u).trans
    dsimp only
    rw [← mul_assoc]
    gcongr

theorem continuous_zetaSquareDivisorContribution (n : ℕ) :
    Continuous (fun t : ℝ => zetaSquareDivisorContribution t n) := by
  unfold zetaSquareDivisorContribution
  apply Continuous.const_mul
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨B, hBint, _, hB⟩ := exists_zetaSquareRightKernel_compact_majorant (|t₀| + 1)
  have hnear : ∀ᶠ t : ℝ in 𝓝 t₀, |t| ≤ |t₀| + 1 :=
    (continuous_abs.continuousAt.eventually
      (gt_mem_nhds (by linarith : |t₀| < |t₀| + 1))).mono (fun _ h => h.le)
  apply continuousAt_of_dominated
    (bound := fun u => ‖divisorDirichletTerm (3 / 2) n‖ * B u)
  · exact Eventually.of_forall (fun t => (integrable_zetaSquareDivisorTerm t n).aestronglyMeasurable)
  · filter_upwards [hnear] with t ht
    filter_upwards with u
    rw [norm_zetaSquareDivisorTerm]
    exact mul_le_mul_of_nonneg_left (hB t ht u) (norm_nonneg _)
  · exact hBint.const_mul _
  · exact Eventually.of_forall (fun u => (continuous_zetaSquareDivisorTerm_height n u).continuousAt)

theorem exists_zetaSquareDivisorContribution_compact_bound (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ M → ∀ n : ℕ,
      ‖zetaSquareDivisorContribution t n‖ ≤ C * ‖divisorDirichletTerm (3 / 2) n‖ := by
  obtain ⟨B, hBint, hB0, hB⟩ := exists_zetaSquareRightKernel_compact_majorant M
  refine ⟨‖(1 / (2 * Real.pi) : ℂ)‖ * ∫ u : ℝ, B u,
    mul_nonneg (norm_nonneg _) (integral_nonneg hB0), ?_⟩
  intro t ht n
  unfold zetaSquareDivisorContribution
  rw [norm_mul]
  calc
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ * (∫ u : ℝ, ‖zetaSquareDivisorTerm t n u‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = ‖(1 / (2 * Real.pi) : ℂ)‖ *
        (‖divisorDirichletTerm (3 / 2) n‖ * ∫ u : ℝ, ‖zetaSquareRightKernel t u‖) := by
      rw [integral_norm_zetaSquareDivisorTerm]
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        (‖divisorDirichletTerm (3 / 2) n‖ * ∫ u : ℝ, B u) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (integral_mono (integrable_zetaSquareRightKernel t).norm hBint (hB t ht))
        (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem continuous_zetaSquareGammaNormalization : Continuous zetaSquareGammaNormalization := by
  have hGamma : Continuous (fun t : ℝ => Gammaℝ (afeCriticalPoint t)) := by
    convert continuous_GammaR_afe_vertical 0 (c := 0) (by norm_num) using 1
    simp [afeCriticalPoint]
  exact hGamma.mul (hGamma.comp continuous_neg)

theorem continuous_zetaSquareNormalizedContribution (n : ℕ) :
    Continuous (fun t : ℝ => zetaSquareNormalizedContribution t n) := by
  exact ((continuous_zetaSquareDivisorContribution n).add
    ((continuous_zetaSquareDivisorContribution n).comp continuous_neg)).div₀
    continuous_zetaSquareGammaNormalization zetaSquareGammaNormalization_ne_zero

theorem exists_zetaSquareNormalizedContribution_compact_bound (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ M → ∀ n : ℕ,
      ‖zetaSquareNormalizedContribution t n‖ ≤ C * ‖divisorDirichletTerm (3 / 2) n‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_zetaSquareDivisorContribution_compact_bound M
  have hInv := continuous_zetaSquareGammaNormalization.inv₀
    zetaSquareGammaNormalization_ne_zero
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-M) M) hInv.continuousOn
  refine ⟨2 * C * max D 0, by positivity, ?_⟩
  intro t ht n
  have hD' : ‖(zetaSquareGammaNormalization t)⁻¹‖ ≤ max D 0 :=
    (hD t (abs_le.mp ht)).trans (le_max_left _ _)
  have hneg := hC (-t) (by simpa only [abs_neg] using ht) n
  unfold zetaSquareNormalizedContribution
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (‖zetaSquareDivisorContribution t n‖ + ‖zetaSquareDivisorContribution (-t) n‖) *
        ‖(zetaSquareGammaNormalization t)⁻¹‖ :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ ≤ (C * ‖divisorDirichletTerm (3 / 2) n‖ + C * ‖divisorDirichletTerm (3 / 2) n‖) *
        max D 0 := by gcongr; exact hC t ht n
    _ = _ := by ring

theorem summable_local_integral_norm_zetaSquareNormalizedContribution (a b : ℝ) :
    Summable (fun n : ℕ => ∫ t in Ioc a b, ‖zetaSquareNormalizedContribution t n‖) := by
  obtain ⟨C, _, hC⟩ := exists_zetaSquareNormalizedContribution_compact_bound (|a| + |b|)
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (f := fun n : ℕ => volume.real (Ioc a b) * (C * ‖divisorDirichletTerm (3 / 2) n‖))
  · intro n
    have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
        ‖zetaSquareNormalizedContribution t n‖ ≤ C * ‖divisorDirichletTerm (3 / 2) n‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply hC t _ n
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b, ht.1, ht.2]
    have hInt := (continuous_zetaSquareNormalizedContribution n).norm.intervalIntegrable (μ := volume) a b
    have h := integral_mono_ae hInt.1 (integrable_const _) hbound
    simpa only [setIntegral_const, smul_eq_mul] using h
  · exact ((summable_divisorDirichletTerm (s := (3 / 2 : ℂ)) (by norm_num)).norm.mul_left C).mul_left _

/-- The complete coefficientwise local integrals sum to the actual local
second moment. The sum--integral exchange is justified before identifying
the sum by the source entry. -/
theorem hasSum_zetaSquareLocalMean {a b : ℝ} (hab : a ≤ b) :
    HasSum (fun n : ℕ => ∫ t in a..b, zetaSquareNormalizedContribution t n)
      ((∫ t in a..b, zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun n => ((continuous_zetaSquareNormalizedContribution n).intervalIntegrable a b).1)
    (summable_local_integral_norm_zetaSquareNormalizedContribution a b)
  simp_rw [(hasSum_zetaSquareNormalizedContribution _).tsum_eq] at h
  simpa only [intervalIntegral.integral_of_le hab, integral_complex_ofReal] using h

theorem zetaSquareLocalMean_eq_divisor_series {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, zetaMomentCriticalNorm t ^ 2) =
      (∑' n : ℕ, ∫ t in a..b, zetaSquareNormalizedContribution t n).re := by
  rw [(hasSum_zetaSquareLocalMean hab).tsum_eq, Complex.ofReal_re]

end MathCollab.Density.Stronger.Atkinson
