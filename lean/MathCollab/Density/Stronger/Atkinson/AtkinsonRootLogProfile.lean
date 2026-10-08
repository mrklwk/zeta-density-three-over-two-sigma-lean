module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.QuadraticGaussian
public import Mathlib

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonRootLogProfile (u : ℝ) : ℝ := 2 * Real.log u + Real.log (2 * Real.pi)

theorem zetaQuadraticLogGaussian_root_rescale {T u : ℝ}
    (hT : 0 < T) (hu : 0 < u) (G : ℝ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi))) =
        zetaGaussianQuadraticIntegral T G (atkinsonRootLogProfile u) := by
  unfold atkinsonRootLogProfile
  congr 1
  rw [Real.log_mul hT.ne' (pow_ne_zero 2 hu.ne'), Real.log_pow,
    Real.log_div hT.ne' (by positivity : 2 * Real.pi ≠ 0)]
  ring


end MathCollab.Density.Stronger.Atkinson
