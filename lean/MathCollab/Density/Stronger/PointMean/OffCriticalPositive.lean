module
-- Reversible module-visibility port of the audited development.
/-
Selected actual positive off-critical estimate adapted from Scott McColm,
PointMeanOffCriticalStrong.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The literal two-pole identity, uniform harmless-term bounds and critical
weighted integrability are proved imports, not analytic hypotheses.
-/
public import MathCollab.Density.Stronger.PointMean.MellinShift
public import MathCollab.Density.Stronger.PointMean.MellinBounds
public import MathCollab.Density.Stronger.PointMean.ExponentialMoments

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

theorem exists_heathBrown_Gamma_shift_kernel_strong_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta v : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      (delta + |v|) * ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |v|) ∧
      (delta + |v|) * ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |v|) := by
  refine ⟨144, by norm_num, ?_⟩
  intro delta v hdelta hdelta'
  exact heathBrown_Gamma_shift_kernel_strong_bound hdelta (by linarith)

noncomputable def heathBrownStrongMellinCriticalMoment
    (delta t : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

theorem integrable_heathBrownStrongMellinCriticalMoment
    {delta t : ℝ} (hdelta : 0 < delta) :
    Integrable (fun u : ℝ =>
      Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
  apply (integrable_heathBrownMellinCriticalMoment
    (delta := delta) (t := t) hdelta).mono'
  · have hcont : Continuous (fun u : ℝ =>
        Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
          zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
      apply Continuous.mul
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro u hu
          exact (by positivity : 0 < delta + |u|).ne' hu
      · exact (continuous_zetaMomentCriticalNorm.pow 2).comp (by fun_prop)
    exact hcont.aestronglyMeasurable
  · filter_upwards with u
    have hexp : Real.exp (-(4 / 3 : ℝ) * |u|) ≤ Real.exp (-|u|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg u]
    have hstrong : 0 ≤
        Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
          zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hstrong]
    gcongr

theorem heathBrownStrongMellinCriticalMoment_nonneg
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 ≤ heathBrownStrongMellinCriticalMoment delta t := by
  unfold heathBrownStrongMellinCriticalMoment
  exact integral_nonneg fun u => by positivity

theorem exists_norm_heathBrown_leftMellinIntegrand_strong_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t u : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)
          (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * (Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
          zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hKernel⟩ :=
    exists_heathBrown_Gamma_shift_kernel_strong_bound
  refine ⟨C, hC, ?_⟩
  intro delta t u hdelta hdeltaUpper
  have hdenom : 0 < delta + |u| := by positivity
  have hGamma :
      ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) := by
    apply (le_div_iff₀ hdenom).2
    simpa only [mul_comm] using
      (hKernel delta u hdelta hdeltaUpper).2
  have harg :
      (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I) +
          (((-delta : ℝ) : ℂ) + (u : ℂ) * I) =
        ((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow, harg]
  change _ * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤ _
  calc
    ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
      (C * Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|)) *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) := by gcongr
    _ = C * (Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by ring

theorem exists_norm_heathBrown_leftVertical_strong_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖VerticalIntegral'
          (heathBrownZetaSquareMellinIntegrand
            (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)) (-delta)‖ ≤
        C * heathBrownStrongMellinCriticalMoment delta t := by
  obtain ⟨B, hB, hPoint⟩ :=
    exists_norm_heathBrown_leftMellinIntegrand_strong_le
  let D : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖
  let C : ℝ := D * B
  have hD : 0 < D := by
    dsimp only [D]
    rw [norm_pos_iff]
    apply one_div_ne_zero
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  refine ⟨C, mul_pos hD hB, ?_⟩
  intro delta t hdelta hdeltaUpper
  let s : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I
  let f : ℝ → ℂ := fun u =>
    heathBrownZetaSquareMellinIntegrand s
      (((-delta : ℝ) : ℂ) + (u : ℂ) * I)
  let g : ℝ → ℝ := fun u => Real.exp (-(4 / 3 : ℝ) * |u|) /
    (delta + |u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)
  have hf : Integrable f := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_minus
      (s := s) hdelta hdeltaUpper
    · dsimp only [s]
      simp
      norm_num
    · dsimp only [s]
      simp
  have hg : Integrable g := by
    simpa only [g] using
      integrable_heathBrownStrongMellinCriticalMoment
        (delta := delta) (t := t) hdelta
  have hIntegral : (∫ u : ℝ, ‖f u‖) ≤ B * ∫ u : ℝ, g u := by
    calc
      (∫ u : ℝ, ‖f u‖) ≤ ∫ u : ℝ, B * g u := by
        apply integral_mono hf.norm (hg.const_mul B)
        intro u
        simpa only [f, g, s] using hPoint delta t u hdelta hdeltaUpper
      _ = B * ∫ u : ℝ, g u := integral_const_mul B g
  unfold VerticalIntegral' VerticalIntegral
  rw [norm_smul, norm_smul]
  simp only [norm_I, one_mul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖∫ u : ℝ, f u‖ ≤
        D * ∫ u : ℝ, ‖f u‖ := by
      dsimp only [D]
      gcongr
      exact norm_integral_le_integral_norm f
    _ ≤ D * (B * ∫ u : ℝ, g u) :=
      mul_le_mul_of_nonneg_left hIntegral hD.le
    _ = C * heathBrownStrongMellinCriticalMoment delta t := by
      dsimp only [C, D]
      unfold heathBrownStrongMellinCriticalMoment
      change _ = (_ * B) * ∫ u : ℝ, g u
      ring

theorem exists_heathBrown_offCritical_plus_strong_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * (1 + heathBrownStrongMellinCriticalMoment delta t) := by
  obtain ⟨R, hR, hResidue⟩ :=
    exists_norm_heathBrownMovingPoleResidue_le
  obtain ⟨V, hV, hVertical⟩ :=
    exists_norm_heathBrown_leftVertical_strong_le
  let S : ℝ := heathBrownSmoothedDivisorMajorant
  let C : ℝ := S + R + V + 1
  have hS : 0 ≤ S := heathBrownSmoothedDivisorMajorant_nonneg
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro delta t hdelta hdeltaUpper ht
  let s : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I
  let m : ℝ := heathBrownStrongMellinCriticalMoment delta t
  have hsRe : s.re = 1 / 2 + delta := by simp [s]
  have hEq := heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical
    (s := s) hdelta hdeltaUpper hsRe
  have hSeries : ‖heathBrownSmoothedDivisorSeries s‖ ≤ S :=
    norm_heathBrownSmoothedDivisorSeries_le (by rw [hsRe]; linarith)
  have hRes : ‖heathBrownMovingPoleResidue s‖ ≤ R := by
    simpa only [s] using hResidue delta t hdelta hdeltaUpper ht
  have hVert :
      ‖VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)‖ ≤
        V * m := by
    simpa only [s, m] using hVertical delta t hdelta hdeltaUpper
  have hm : 0 ≤ m := heathBrownStrongMellinCriticalMoment_nonneg hdelta
  change ‖riemannZeta s‖ ^ (2 : ℕ) ≤ C * (1 + m)
  rw [← norm_pow, hEq]
  calc
    ‖heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)‖ ≤
      ‖heathBrownSmoothedDivisorSeries s‖ +
        ‖heathBrownMovingPoleResidue s‖ +
        ‖VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)‖ := by
      have hOuter := norm_sub_le
        (heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s)
        (VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta))
      have hInner := norm_sub_le
        (heathBrownSmoothedDivisorSeries s) (heathBrownMovingPoleResidue s)
      linarith
    _ ≤ S + R + V * m := by linarith
    _ ≤ C * (1 + m) := by
      dsimp only [C]
      nlinarith [mul_nonneg hS hm, mul_nonneg hR.le hm, mul_nonneg hV.le hm]


end MathCollab.Density.Stronger.PointMean
