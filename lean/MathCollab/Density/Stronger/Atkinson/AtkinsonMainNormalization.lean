module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_SIGNED_NORMALIZATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonEvaluatedPhases
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleProfileNormalization

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonStationaryMain_sqrt_normalized {T : ℝ} (hT : 0 < T)
    (G L : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L (1/4) (Real.sqrt n) =
      2*(atkinsonCommonSaddleFactor T (Real.sqrt n) : ℂ) *
        atkinsonSaddleResidual T G L (Real.sqrt n) * zetaSquareReflectedGammaPhase T *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((atkinsonSourcePhase T n : ℂ)*I) := by
  rw [atkinsonStationaryMain_sqrt hT]
  calc
    _ = 2*(atkinsonSaddleProfile T G L (1/4) (Real.sqrt n) /
      (Real.sqrt (2*atkinsonSaddleCurvature T (Real.sqrt n)) : ℂ)) *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((atkinsonSourcePhase T n : ℂ)*I) := by ring
    _ = _ := by rw [atkinsonSaddleProfile_div_curvature hT]; ring

theorem atkinsonStationaryMain_neg_sqrt_normalized {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L (1/4) (-Real.sqrt n) =
      (-I)*2*(atkinsonCommonSaddleFactor T (Real.sqrt n) : ℂ) *
        atkinsonSaddleResidual T G L (-Real.sqrt n) * zetaSquareReflectedGammaPhase T *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((-atkinsonSourcePhase T n : ℂ)*I) := by
  rw [atkinsonStationaryMain_neg_sqrt hT hG]
  calc
    _ = (-I)*2*(atkinsonSaddleProfile T G L (1/4) (-Real.sqrt n) /
      (Real.sqrt (2*atkinsonSaddleCurvature T (-Real.sqrt n)) : ℂ)) *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((-atkinsonSourcePhase T n : ℂ)*I) := by ring
    _ = _ := by
      rw [atkinsonSaddleProfile_div_curvature hT,atkinsonCommonSaddleFactor_neg]
      ring

end MathCollab.Density.Stronger.Atkinson
