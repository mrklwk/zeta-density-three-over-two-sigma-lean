module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCompactProfiles
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaQuadraticLogGaussianVariation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex Set
open scoped ContDiff
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonPowerWeight (T G L α x : ℝ) : ℂ :=
  ((T ^ (-α) : ℝ) : ℂ) * atkinsonPowerProfile α (x / T) *
    (zetaDivisorBandCutoff T G L x : ℂ) * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem exists_intervalC1Bound_atkinsonPowerWeight (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (atkinsonPowerWeight T G L α) (T / 16) T (C * G * T ^ (-α)) := by
  obtain ⟨C, hC, hprofile⟩ := exists_intervalC1Bound_rescaled
    (fun _ hu => contDiffAt_atkinsonPowerProfile α hu)
  refine ⟨128 * C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hG hGT hL
  have hab : T / 16 ≤ T := by linarith
  have ht : IntervalC1Bound (fun _ : ℝ => ((T ^ (-α) : ℝ) : ℂ)) (T / 16) T (T ^ (-α)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hT _)] using
      intervalC1Bound_const ((T ^ (-α) : ℝ) : ℂ) (T / 16) T
  have hp : IntervalC1Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (T / 16) T 1 := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC1Bound_const (zetaSquareReflectedGammaPhase T) (T / 16) T
  have h := (((ht.mul (hprofile T hT) hab).mul
    (intervalC1Bound_zetaDivisorBandCutoff hT hG hL hab) hab).mul hp hab).mul
      (intervalC1Bound_zetaQuadraticLogGaussian hT hG hGT) hab
  convert h using 1
  · rfl
  · ring

end MathCollab.Density.Stronger.Atkinson
