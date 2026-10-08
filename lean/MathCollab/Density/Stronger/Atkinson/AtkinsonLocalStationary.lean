module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalQuadratic
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNaturalAmplitude
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_atkinsonPowerIntegral_local_quadratic_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 ≤ H →
      Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
      ‖2 * (∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H),
            atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y) -
        2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
          ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
            (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
        C * G * T ^ (-α) * (4 * (G / Real.sqrt T) * H ^ 2 +
          16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural α
  refine ⟨C, hC, ?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have h := (hbound T G L hT hG hGT hL hwidth).atkinsonLocalQuadratic
    hT b hH hleft hright hwindow
  have he (x y z : ℂ) : 2 * x - 2 * y * z = 2 * (x - y * z) := by ring
  rw [he, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring


end MathCollab.Density.Stronger.Atkinson
