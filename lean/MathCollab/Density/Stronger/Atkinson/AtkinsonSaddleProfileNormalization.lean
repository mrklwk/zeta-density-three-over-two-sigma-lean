module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_SIGNED_NORMALIZATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSignedSaddleProfile
public import MathCollab.Density.Stronger.Atkinson.AtkinsonQuadraticKernel
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCoefficientVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonResidualVariation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonSaddle_quarter_power_curvature {T : ℝ} (hT : 0 < T) (b : ℝ) :
    T^(-(1/4 : ℝ)) * (zetaAtkinsonSaddle T b/T)^(-(1/4 : ℝ)) /
      Real.sqrt (2*atkinsonSaddleCurvature T b) = atkinsonCommonSaddleFactor T b := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hc : 0 < atkinsonSaddleCurvature T b := by
    linarith [one_lt_atkinsonSaddleCurvature hT b]
  have hp : T^(-(1/4 : ℝ)) * (zetaAtkinsonSaddle T b/T)^(-(1/4 : ℝ)) =
      (Real.sqrt r)⁻¹ := by
    rw [← Real.mul_rpow hT.le (by unfold zetaAtkinsonSaddle; positivity),
      mul_div_cancel₀ _ hT.ne']
    change (r^2)^(-(1/4 : ℝ)) = _
    rw [← Real.rpow_natCast,← Real.rpow_mul hr.le]
    norm_num only [show (2:ℝ)*(-(1/4:ℝ)) = -(1/2) by norm_num]
    rw [Real.rpow_neg hr.le,← Real.sqrt_eq_rpow]
  have hs := atkinsonSaddle_squareRoot_normalization hT b
  change Real.sqrt (atkinsonSaddleCurvature T b) * Real.sqrt r = _ at hs
  rw [hp,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  change _ = 1/(Real.sqrt 2 * Real.sqrt (Real.sqrt (b^2+4*(T/(2*Real.pi)))))
  calc
    _ = 1/(Real.sqrt 2*(Real.sqrt (atkinsonSaddleCurvature T b)*Real.sqrt r)) := by ring
    _ = _ := by rw [hs]

theorem atkinsonSaddleProfile_div_curvature {T : ℝ} (hT : 0 < T) (G L b : ℝ) :
    atkinsonSaddleProfile T G L (1/4) b /
      (Real.sqrt (2*atkinsonSaddleCurvature T b) : ℂ) =
        (atkinsonCommonSaddleFactor T b : ℂ) *
          atkinsonSaddleResidual T G L b * zetaSquareReflectedGammaPhase T := by
  have he : ((T^(-(1/4:ℝ)) : ℝ) : ℂ) *
      (((zetaAtkinsonSaddle T b/T)^(-(1/4:ℝ)) : ℝ) : ℂ) /
        (Real.sqrt (2*atkinsonSaddleCurvature T b) : ℂ) =
          (atkinsonCommonSaddleFactor T b : ℂ) := by
    exact_mod_cast atkinsonSaddle_quarter_power_curvature hT b
  unfold atkinsonSaddleProfile atkinsonPowerProfile atkinsonSaddleResidual
  calc
    _ = (((T^(-(1/4:ℝ)) : ℝ) : ℂ) *
      (((zetaAtkinsonSaddle T b/T)^(-(1/4:ℝ)) : ℝ) : ℂ) /
        (Real.sqrt (2*atkinsonSaddleCurvature T b) : ℂ)) *
      (zetaMainMellinProfile (zetaAtkinsonSaddle T b/T) *
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ)) *
          zetaSquareReflectedGammaPhase T := by ring
    _ = _ := by rw [he]

end MathCollab.Density.Stronger.Atkinson
