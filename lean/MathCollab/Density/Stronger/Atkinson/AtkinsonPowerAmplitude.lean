module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerWeight
public import MathCollab.Density.Stronger.Atkinson.AtkinsonAmplitude

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex Set
namespace MathCollab.Density.Stronger.Atkinson

theorem sqrt_mul_exp_neg_half_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * Real.exp (-Real.log x / 2) = 1 := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem atkinsonPowerWeight_eq_amplitude {T x : ℝ} (hT : 0 < T) (hx : 0 < x)
    (G L α : ℝ) :
    atkinsonPowerWeight T G L α x =
      (Real.sqrt x : ℂ) * ((x ^ (-α) : ℝ) : ℂ) * zetaAtkinsonAmplitude T G L x := by
  have he : T ^ (-α) * (x / T) ^ (-α) = x ^ (-α) := by
    rw [← Real.mul_rpow hT.le (by positivity), mul_div_cancel₀ _ hT.ne']
  have hs : (Real.sqrt x : ℂ) * (Real.exp (-Real.log x / 2) : ℂ) = 1 := by
    exact_mod_cast sqrt_mul_exp_neg_half_log hx
  unfold atkinsonPowerWeight atkinsonPowerProfile zetaAtkinsonAmplitude
  rw [zetaDivisorWeight_source_eq_profile hT hx]
  have heC : ((T ^ (-α) : ℝ) : ℂ) * (((x / T) ^ (-α) : ℝ) : ℂ) = ((x ^ (-α) : ℝ) : ℂ) := by
    exact_mod_cast he
  calc
    _ = (((T ^ (-α) : ℝ) : ℂ) * (((x / T) ^ (-α) : ℝ) : ℂ)) *
      (zetaMainMellinProfile (x / T) * (zetaDivisorBandCutoff T G L x : ℂ) *
        zetaSquareReflectedGammaPhase T *
          zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))) := by ring
    _ = _ := by
      rw [heC]
      linear_combination -((x ^ (-α) : ℝ) : ℂ) * zetaMainMellinProfile (x / T) *
        (zetaDivisorBandCutoff T G L x : ℂ) * zetaSquareReflectedGammaPhase T *
          zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi))) * hs


end MathCollab.Density.Stronger.Atkinson
