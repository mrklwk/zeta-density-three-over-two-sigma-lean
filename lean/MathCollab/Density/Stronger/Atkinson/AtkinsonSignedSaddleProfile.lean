module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_SIGNED_NORMALIZATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleGaussianIdentities
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerWeight
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSaddleProfile (T G L α b : ℝ) : ℂ :=
  ((T ^ (-α) : ℝ) : ℂ) *
    atkinsonPowerProfile α (zetaAtkinsonSaddle T b / T) *
      (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ) *
        zetaSquareReflectedGammaPhase T

theorem atkinsonRootKernel_at_saddle {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) =
      Complex.exp ((zetaAtkinsonPhase T b (zetaAtkinsonSaddle T b) : ℂ) * I) := by
  rw [zetaAtkinsonSaddle, zetaAtkinsonPhase_sq T b (atkinsonSaddleRoot_pos (by positivity) b)]
  unfold atkinsonRootKernel
  congr 1
  push_cast
  ring

theorem atkinsonPowerWeight_at_saddle {T : ℝ} (hT : 0 < T) (G L α : ℝ) (n : ℕ) :
    atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (Real.sqrt n)) =
      atkinsonSaddleProfile T G L α (Real.sqrt n) * atkinsonSaddleGaussian T G n := by
  unfold atkinsonPowerWeight atkinsonSaddleProfile
  rw [zetaGaussianQuadraticIntegral_at_saddle hT G n]

theorem atkinsonPowerWeight_at_neg_saddle {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α : ℝ) (n : ℕ) :
    atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (-Real.sqrt n)) =
      atkinsonSaddleProfile T G L α (-Real.sqrt n) * atkinsonSaddleGaussian T G n := by
  unfold atkinsonPowerWeight atkinsonSaddleProfile
  rw [zetaGaussianQuadraticIntegral_at_neg_saddle hT hG n]

end MathCollab.Density.Stronger.Atkinson
