module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerWeight
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNaturalGaussianProfile
public import MathCollab.Density.Stronger.Atkinson.ZetaBandPhysicalDerivatives

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_intervalC2Bound_atkinsonPowerWeight_normalized_natural (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (fun u => atkinsonPowerWeight T G L α (T * u ^ 2))
        (1 / 4) 1 (C * G * T ^ (-α)) G := by
  obtain ⟨A, hA, hprofile⟩ := exists_intervalC2Bound_atkinsonPowerRootProfile α
  obtain ⟨B, hB, hcutoff⟩ := exists_intervalC2Bound_zetaDivisorBandCutoff_root
  obtain ⟨D, hD, hgaussian⟩ := exists_intervalC2Bound_zetaQuadraticLogGaussian_root_natural
  let K : ℝ := 1 + 2 * Real.pi * Real.exp 1
  have hK : 1 ≤ K := by dsimp [K]; have := Real.exp_pos (1 : ℝ); nlinarith [Real.pi_pos]
  refine ⟨256 * A * B * K ^ 2 * D, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hG0 : 0 < G := by linarith
  have hc : IntervalC2Bound (fun u => (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ))
      (1 / 4) 1 (B * K ^ 2) G :=
    (hcutoff T G L hT hG0 hL hwidth).absorb_scale hK hG0.le
  have ht : IntervalC2Bound (fun _ : ℝ => ((T ^ (-α) : ℝ) : ℂ))
      (1 / 4) 1 (T ^ (-α)) G := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hT _)] using
      intervalC2Bound_const ((T ^ (-α) : ℝ) : ℂ) (1 / 4) 1 hG0.le
  have hg : IntervalC2Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (1 / 4) 1 1 G := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC2Bound_const (zetaSquareReflectedGammaPhase T) (1 / 4) 1 hG0.le
  have h := (((ht.mul (hprofile.mono le_rfl hG)).mul hc).mul hg).mul (hgaussian T G hT hG hGT)
  have he : (fun u => atkinsonPowerWeight T G L α (T * u ^ 2)) =
      fun u => ((T ^ (-α) : ℝ) : ℂ) * atkinsonPowerProfile α (u ^ 2) *
        (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ) * zetaSquareReflectedGammaPhase T *
          zetaGaussianQuadraticIntegral T G (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi))) := by
    funext u
    unfold atkinsonPowerWeight
    rw [show T * u ^ 2 / T = u ^ 2 by field_simp]
  rw [he]
  convert h using 1
  ring

theorem exists_intervalC2Bound_atkinsonPowerWeight_root_natural (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (fun y => atkinsonPowerWeight T G L α (y ^ 2))
        (Real.sqrt T / 4) (Real.sqrt T) (C * G * T ^ (-α)) (G / Real.sqrt T) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonPowerWeight_normalized_natural α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have h := (hbound T G L hT hG hGT hL hwidth).comp_div hs
  have he : (fun y => atkinsonPowerWeight T G L α (T * (y / Real.sqrt T) ^ 2)) =
      fun y => atkinsonPowerWeight T G L α (y ^ 2) := by
    funext y
    congr 1
    rw [div_pow, Real.sq_sqrt hT.le]
    field_simp
  simpa only [he, mul_one, mul_one_div] using h


end MathCollab.Density.Stronger.Atkinson
