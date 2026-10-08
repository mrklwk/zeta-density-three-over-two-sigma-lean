module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryReduction

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonFiniteStationaryMain (T G L α b H : ℝ) : ℂ :=
  2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
    atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
      atkinsonQuadraticWindow (atkinsonSaddleCurvature T b) H

theorem atkinsonFiniteStationaryMain_eq_quadratic (T G L α b H : ℝ) :
    atkinsonFiniteStationaryMain T G L α b H =
      2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
        ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y := by
  rw [integral_atkinsonRootQuadraticKernel]
  unfold atkinsonFiniteStationaryMain
  ring

theorem exists_atkinsonPowerIntegral_finite_stationary_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H →
      Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
      ‖atkinsonPowerIntegral T G L α b - atkinsonFiniteStationaryMain T G L α b H‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
          16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  simpa only [atkinsonFiniteStationaryMain_eq_quadratic] using
    exists_atkinsonPowerIntegral_quadratic_approximation α


end MathCollab.Density.Stronger.Atkinson
