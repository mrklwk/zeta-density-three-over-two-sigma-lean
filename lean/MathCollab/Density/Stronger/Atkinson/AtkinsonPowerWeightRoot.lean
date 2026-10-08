module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerWeight
public import MathCollab.Density.Stronger.Atkinson.AtkinsonAmplitudeIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex Set
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_intervalC1Bound_atkinsonPowerWeight_root (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (fun y => atkinsonPowerWeight T G L α (y ^ 2))
        (Real.sqrt T / 4) (Real.sqrt T) (C * G * T ^ (-α)) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC1Bound_atkinsonPowerWeight α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL
  have hsq : (Real.sqrt T / 4) ^ 2 = T / 16 := by
    rw [div_pow, Real.sq_sqrt hT.le]
    norm_num
  have hf : IntervalC1Bound (atkinsonPowerWeight T G L α)
      ((Real.sqrt T / 4) ^ 2) ((Real.sqrt T) ^ 2) (C * G * T ^ (-α)) := by
    rw [hsq, Real.sq_sqrt hT.le]
    exact hbound T G L hT hG hGT hL
  exact hf.comp_sq (by positivity) (by nlinarith [Real.sqrt_nonneg T])


end MathCollab.Density.Stronger.Atkinson
