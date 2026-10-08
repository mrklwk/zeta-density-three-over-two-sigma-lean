module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootBand

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Cancellation outside the actual source-scale frequency band

The slope is controlled on the exact smooth source support, not the much
larger height-sized interval. Both signed carriers consume that geometry.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonRootSlope_outside_band {T G L b y : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hy : y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L))
    (hb : 6 * Real.sqrt T * (L / G) ≤ b) :
    b ≤ atkinsonRootSlope T b y ∧ atkinsonRootSlope T (-b) y ≤ -b := by
  have h := abs_le.mp (abs_atkinsonRootSlope_zero_le_band hT hG hL hwidth hy)
  have hp : atkinsonRootSlope T b y = atkinsonRootSlope T 0 y + 2 * b := by
    unfold atkinsonRootSlope
    ring
  have hn : atkinsonRootSlope T (-b) y = atkinsonRootSlope T 0 y - 2 * b := by
    unfold atkinsonRootSlope
    ring
  rw [hp, hn]
  constructor <;> linarith [h.1, h.2]

theorem norm_atkinsonRootKernel_integral_outside_band {T G L b c : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hc : c ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L))
    (hb : 6 * Real.sqrt T * (L / G) ≤ b) :
    ‖∫ y in atkinsonRootBandLower T G L..c, atkinsonRootKernel T b y‖ ≤ 1 / (b * Real.pi) ∧
      ‖∫ y in atkinsonRootBandLower T G L..c, atkinsonRootKernel T (-b) y‖ ≤
        1 / (b * Real.pi) := by
  have ha := atkinsonRootBandLower_pos hT G L
  have hb0 : 0 < b := (by positivity : 0 < 6 * Real.sqrt T * (L / G)).trans_le hb
  have hmem (y : ℝ) (hy : y ∈ Icc (atkinsonRootBandLower T G L) c) :
      y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L) :=
    ⟨hy.1, hy.2.trans hc.2⟩
  have hd (u y : ℝ) (hy : y ∈ Icc (atkinsonRootBandLower T G L) c) :
      deriv (atkinsonRootPhase T u) y = atkinsonRootSlope T u y :=
    (hasDerivAt_atkinsonRootPhase T u (ha.trans_le hy.1)).deriv
  have hmono (u : ℝ) : AntitoneOn (deriv (atkinsonRootPhase T u))
      (Icc (atkinsonRootBandLower T G L) c) := by
    intro x hx y hy hxy
    rw [hd u x hx, hd u y hy]
    exact (atkinsonRootSlope_strictAnti hT.le u).antitoneOn
      (ha.trans_le hx.1) (ha.trans_le hy.1) hxy
  constructor
  · exact norm_phaseIntegral_le_of_positive_slope hc.1 hb0
      (fun y hy => contDiffAt_atkinsonRootPhase T b (ha.trans_le hy.1))
      (fun y hy => by
        rw [hd b y hy]
        exact (atkinsonRootSlope_outside_band hT hG hL hwidth (hmem y hy) hb).1)
      (hmono b)
  · exact norm_phaseIntegral_le_of_negative_slope hc.1 hb0
      (fun y hy => contDiffAt_atkinsonRootPhase T (-b) (ha.trans_le hy.1))
      (fun y hy => by
        rw [hd (-b) y hy]
        exact (atkinsonRootSlope_outside_band hT hG hL hwidth (hmem y hy) hb).2)
      (hmono (-b))

theorem exists_intervalC1Bound_atkinsonPowerWeight_root_band (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
      IntervalC1Bound (fun y => atkinsonPowerWeight T G L α (y ^ 2))
        (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L) (C * G * T ^ (-α)) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC1Bound_atkinsonPowerWeight_root α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs := atkinsonRootBand_physical hT hG hL.le hwidth
  have hlo : Real.sqrt T / 4 ≤ atkinsonRootBandLower T G L := by
    convert hs.1 using 1
    rw [Real.sqrt_div hT.le]
    norm_num
  exact (hbound T G L hT hG hGT hL).restrict hlo
    (atkinsonRootBand_order hT hG hL.le) hs.2

theorem exists_norm_atkinsonPowerIntegral_outside_band_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → 6 * Real.sqrt T * (L / G) ≤ b →
      ‖atkinsonPowerIntegral T G L α b‖ ≤ C * G * T ^ (-α) / b ∧
        ‖atkinsonPowerIntegral T G L α (-b)‖ ≤ C * G * T ^ (-α) / b := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC1Bound_atkinsonPowerWeight_root_band α
  refine ⟨4 * C / Real.pi, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth hb
  have ha := atkinsonRootBandLower_pos hT G L
  have hab := atkinsonRootBand_order hT hG hL.le
  have hf := hbound T G L hT hG hGT hL hwidth
  have hp (u : ℝ)
      (hu : ∀ x ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L),
        ‖∫ y in atkinsonRootBandLower T G L..x, atkinsonRootKernel T u y‖ ≤ 1 / (b * Real.pi)) :
      ‖atkinsonPowerIntegral T G L α u‖ ≤ (4 * C / Real.pi) * G * T ^ (-α) / b := by
    have h := hf.atkinsonRoot_of_primitive_bound u ha hab hu
    rw [atkinsonPowerIntegral_eq_root_band hT hG hL α u, norm_mul, norm_ofNat]
    have hfin := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    convert hfin using 1
    ring
  exact ⟨hp b (fun x hx => (norm_atkinsonRootKernel_integral_outside_band hT hG hL hwidth hx hb).1),
    hp (-b) (fun x hx => (norm_atkinsonRootKernel_integral_outside_band hT hG hL hwidth hx hb).2)⟩

end MathCollab.Density.Stronger.Atkinson
