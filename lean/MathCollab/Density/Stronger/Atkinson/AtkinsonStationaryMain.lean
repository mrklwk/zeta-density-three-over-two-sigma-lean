module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFiniteStationaryMain

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Evaluated stationary main term for the actual carrier

The previously retained finite quadratic window is replaced using the proved
Fresnel tail, with its actual curvature and constructed saddle amplitude.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonStationaryMain (T G L α b : ℝ) : ℂ :=
  2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
    atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
      fresnelGaussianValue (atkinsonSaddleCurvature T b)

theorem atkinsonStationaryMain_eq_phase {T : ℝ} (hT : 0 < T) (G L α b : ℝ) :
    atkinsonStationaryMain T G L α b =
      2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
        atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
          (Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T b) : ℂ)) := by
  unfold atkinsonStationaryMain
  rw [fresnelGaussianValue_eq_phase (by linarith [one_lt_atkinsonSaddleCurvature hT b])]

theorem exists_norm_atkinsonFiniteStationaryMain_sub_main_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      0 < H → atkinsonSaddleRoot (T / (2 * Real.pi)) b ∈
        Icc (Real.sqrt T / 4) (Real.sqrt T) →
      ‖atkinsonFiniteStationaryMain T G L α b H - atkinsonStationaryMain T G L α b‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi)) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC1Bound_atkinsonPowerWeight_root α
  refine ⟨C, hC, ?_⟩
  intro T G L b H hT hG hGT hL hH hr
  have hc : 1 < atkinsonSaddleCurvature T b := one_lt_atkinsonSaddleCurvature hT b
  have hW := (hbound T G L hT hG hGT hL).norm_le _ hr
  have hF := norm_atkinsonQuadraticWindow_sub_gaussianValue_le (by linarith : 0 <
    atkinsonSaddleCurvature T b) hH
  have htail : 2 / (atkinsonSaddleCurvature T b * H * Real.pi) ≤ 2 / (H * Real.pi) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [mul_pos hH Real.pi_pos]
  unfold atkinsonFiniteStationaryMain atkinsonStationaryMain
  rw [← mul_sub, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_atkinsonRootKernel, mul_one]
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hW (by norm_num : (0 : ℝ) ≤ 2))
    (hF.trans htail) (norm_nonneg _) (by positivity)).trans_eq
  ring

theorem exists_atkinsonPowerIntegral_stationary_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H →
      Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
      ‖atkinsonPowerIntegral T G L α b - atkinsonStationaryMain T G L α b‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
          16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  obtain ⟨A, hA, hfinite⟩ := exists_atkinsonPowerIntegral_finite_stationary_approximation α
  obtain ⟨B, hB, hmain⟩ := exists_norm_atkinsonFiniteStationaryMain_sub_main_le α
  refine ⟨A + B, by positivity, ?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hf := hfinite T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hm := hmain T G L b H hT hG0 hGT hL0 hH ⟨by linarith, by linarith⟩
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T / (2 * Real.pi)) b
  have hm' : ‖atkinsonFiniteStationaryMain T G L α b H - atkinsonStationaryMain T G L α b‖ ≤
      B * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
        16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have htwo : 0 ≤ 4 * (G / Real.sqrt T) * H ^ 2 := by positivity
    have hthree : 0 ≤ 16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3 := by positivity
    linarith
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hf hm').trans_eq ?_)
  ring

end MathCollab.Density.Stronger.Atkinson
