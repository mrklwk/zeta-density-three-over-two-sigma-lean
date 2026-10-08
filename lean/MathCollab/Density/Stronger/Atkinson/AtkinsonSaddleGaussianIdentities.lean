module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_SIGNED_NORMALIZATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonGaussianVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddlePhase

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem zetaGaussianQuadraticIntegral_neg (T : ℝ) {G : ℝ} (hG : G ≠ 0) (v : ℝ) :
    zetaGaussianQuadraticIntegral T G (-v) = zetaGaussianQuadraticIntegral T G v := by
  rw [zetaGaussianQuadraticIntegral_eq T (-v) hG, zetaGaussianQuadraticIntegral_eq T v hG,
    Complex.ofReal_neg, neg_sq]

theorem zetaGaussianQuadraticIntegral_at_saddle {T : ℝ} (hT : 0 < T) (G : ℝ) (n : ℕ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (zetaAtkinsonSaddle T (Real.sqrt n)) - Real.log (T / (2 * Real.pi))) =
        atkinsonSaddleGaussian T G n := by
  rw [zetaAtkinsonSaddle_log_argument hT, atkinson_sqrt_frequency_normalized hT n]
  rfl

theorem zetaGaussianQuadraticIntegral_at_neg_saddle {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (n : ℕ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (zetaAtkinsonSaddle T (-Real.sqrt n)) - Real.log (T / (2 * Real.pi))) =
        atkinsonSaddleGaussian T G n := by
  rw [zetaAtkinsonSaddle_log_argument hT, neg_div, Real.arsinh_neg, mul_neg,
    zetaGaussianQuadraticIntegral_neg T hG, atkinson_sqrt_frequency_normalized hT n]
  rfl

theorem atkinsonSaddleGaussian_eq (T : ℝ) {G : ℝ} (hG : G ≠ 0) (n : ℕ) :
    atkinsonSaddleGaussian T G n =
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.arsinh (Real.sqrt (Real.pi * (n : ℝ) / (2 * T))) : ℂ) ^ 2) /
          zetaGaussianQuadraticCoefficient T G) := by
  rw [atkinsonSaddleGaussian, zetaGaussianQuadraticIntegral_eq T _ hG]
  congr 2
  push_cast
  ring

end MathCollab.Density.Stronger.Atkinson
