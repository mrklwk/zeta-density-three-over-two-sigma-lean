module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryMain
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSampleGeometry

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Both physical frequencies with the evaluated stationary main term

The physical consumer derives all saddle-window hypotheses. The source
integral and both signs are retained with one common parameter-uniform bound.
-/

noncomputable section

open Complex Set

namespace MathCollab.Density.Stronger.Atkinson

theorem exists_atkinsonPowerIntegral_small_frequency_stationary (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H → H ≤ Real.sqrt T / 12 →
      |b| ≤ Real.sqrt T / 100 →
      ‖atkinsonPowerIntegral T G L α b - atkinsonStationaryMain T G L α b‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
          432 * H ^ 4 / Real.sqrt T) := by
  obtain ⟨C, hC, hbound⟩ := exists_atkinsonPowerIntegral_stationary_approximation α
  refine ⟨C, hC, ?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hHT hb
  obtain ⟨hleft, hright, hwindow⟩ := atkinsonSaddleRoot_small_frequency_window hT hb hHT
  have h := hbound T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T / (2 * Real.pi)) b
  have hlo := (atkinsonSaddleRoot_small_frequency hT hb).1
  have hrem : 16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3 ≤
      432 * H ^ 4 / Real.sqrt T := by
    calc
      _ ≤ 16 * T * H ^ 4 / (Real.sqrt T / 3) ^ 3 := by gcongr
      _ = _ := by
        rw [div_pow, show (Real.sqrt T) ^ 3 = (Real.sqrt T) ^ 2 * Real.sqrt T by ring,
          Real.sq_sqrt hT.le]
        field_simp
        ring
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hrem) (by positivity))

theorem exists_atkinsonPowerIntegral_small_n_pair_stationary (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H → H ≤ Real.sqrt T / 12 →
      ∀ n : ℕ, 10000 * (n : ℝ) ≤ T →
      ‖atkinsonPowerIntegral T G L α (Real.sqrt n) -
        atkinsonStationaryMain T G L α (Real.sqrt n)‖ ≤
          C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
            432 * H ^ 4 / Real.sqrt T) ∧
      ‖atkinsonPowerIntegral T G L α (-Real.sqrt n) -
        atkinsonStationaryMain T G L α (-Real.sqrt n)‖ ≤
          C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
            432 * H ^ 4 / Real.sqrt T) := by
  obtain ⟨C, hC, hbound⟩ := exists_atkinsonPowerIntegral_small_frequency_stationary α
  refine ⟨C, hC, ?_⟩
  intro T G L H hT hG hGT hL hwidth hH hHT n hn
  have hb := sqrt_nat_small_frequency hT n hn
  constructor
  · exact hbound T G L (Real.sqrt n) H hT hG hGT hL hwidth hH hHT hb
  · exact hbound T G L (-Real.sqrt n) H hT hG hGT hL hwidth hH hHT (by simpa only [abs_neg])

end MathCollab.Density.Stronger.Atkinson
