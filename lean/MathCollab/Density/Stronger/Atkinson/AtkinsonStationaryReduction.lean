module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalStationary
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerWeightRoot

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_atkinsonPowerIntegral_quadratic_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H →
      Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
      ‖atkinsonPowerIntegral T G L α b -
        2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
          ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
            (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
          16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  obtain ⟨A, hA, hv⟩ := exists_intervalC1Bound_atkinsonPowerWeight_root α
  obtain ⟨B, hB, hf⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural α
  refine ⟨A + B, by positivity, ?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hAM : A * G * T ^ (-α) ≤ (A + B) * G * T ^ (-α) := by gcongr; linarith
  have hBM : B * G * T ^ (-α) ≤ (A + B) * G * T ^ (-α) := by gcongr; linarith
  have h := ((hf T G L hT hG hGT hL hwidth).mono hBM le_rfl).atkinsonQuadraticApproximation
    ((hv T G L hT hG0 hGT hL0).mono hAM) hT b (by positivity) hH hleft hright hwindow
  have hs : Real.sqrt (T / 16) = Real.sqrt T / 4 := by
    rw [Real.sqrt_div hT.le]
    norm_num
  rw [atkinsonPowerIntegral_eq_root hT hG0 hL0 hwidth α b, hs]
  have he (x y z : ℂ) : 2 * x - 2 * y * z = 2 * (x - y * z) := by ring
  rw [he, norm_mul, Complex.norm_ofNat]
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring


end MathCollab.Density.Stronger.Atkinson
