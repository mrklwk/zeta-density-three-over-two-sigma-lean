module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.FresnelDampedTails
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Actual Gaussian formula with a damping-uniform truncation error

Positive damping supplies genuine Lebesgue integrability. The tail estimate
comes from finite oscillatory intervals and passes to the improper limit.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace MathCollab.Density.Stronger.Atkinson

theorem integrable_fresnelDampedKernel {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable (fresnelDampedKernel ε c) := by
  apply integrable_cexp_neg_mul_sq
  simpa using hε

theorem integral_Ioi_fresnelDampedKernel {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    (∫ x : ℝ in Ioi 0, fresnelDampedKernel ε c x) =
      ((Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) ^ (1 / 2 : ℂ) / 2 := by
  apply integral_gaussian_complex_Ioi
  simpa using hε

theorem norm_integral_Ioi_fresnelDampedKernel_le {ε c H : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hH : 0 < H) :
    ‖∫ x : ℝ in Ioi H, fresnelDampedKernel ε c x‖ ≤ 1 / (c * H * Real.pi) := by
  have hlim := intervalIntegral_tendsto_integral_Ioi H
    (integrable_fresnelDampedKernel hε c).integrableOn tendsto_id
  apply le_of_tendsto hlim.norm
  filter_upwards [eventually_ge_atTop H] with B hB
  exact norm_integral_fresnelDampedKernel_le hε.le hc hH hB

theorem integral_symmetric_fresnelDampedKernel (ε c H : ℝ) :
    (∫ x in (-H)..H, fresnelDampedKernel ε c x) =
      2 * ∫ x in (0 : ℝ)..H, fresnelDampedKernel ε c x := by
  have he : (∫ x in (-H)..0, fresnelDampedKernel ε c x) =
      ∫ x in (0 : ℝ)..H, fresnelDampedKernel ε c x := by
    have h := intervalIntegral.integral_comp_neg (fresnelDampedKernel ε c) (a := -H) (b := 0)
    simp only [fresnelDampedKernel_neg, neg_zero, neg_neg] at h
    exact h
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_fresnelDampedKernel ε c).intervalIntegrable (-H) 0)
    ((continuous_fresnelDampedKernel ε c).intervalIntegrable 0 H), he]
  ring

theorem norm_gaussianValue_sub_fresnelDampedWindow_le {ε c H : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hH : 0 < H) :
    ‖((Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) ^ (1 / 2 : ℂ) -
      ∫ x in (-H)..H, fresnelDampedKernel ε c x‖ ≤ 2 / (c * H * Real.pi) := by
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (integrable_fresnelDampedKernel hε c).integrableOn hH.le
  rw [integral_Ioi_fresnelDampedKernel hε c] at hsplit
  have he : ((Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) ^ (1 / 2 : ℂ) -
      (∫ x in (-H)..H, fresnelDampedKernel ε c x) =
        2 * ∫ x : ℝ in Ioi H, fresnelDampedKernel ε c x := by
    rw [integral_symmetric_fresnelDampedKernel]
    linear_combination 2 * hsplit
  rw [he, norm_mul, Complex.norm_ofNat]
  apply (mul_le_mul_of_nonneg_left
    (norm_integral_Ioi_fresnelDampedKernel_le hε hc hH) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring

end MathCollab.Density.Stronger.Atkinson
