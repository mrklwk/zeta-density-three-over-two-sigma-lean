module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSlopeDerivativeBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Actual band length, vanishing endpoints and quotient amplitude

These are the source hypotheses needed for two integrations by parts.
They are derived from the original cutoff and natural amplitude bounds.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Set

namespace MathCollab.Density.Stronger.Atkinson

theorem sqrt_exp_half (v : ℝ) : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
  have he : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, Real.sqrt_sq (Real.exp_pos _).le]

theorem sqrt_zetaDivisorBandEdge {T : ℝ} (hT : 0 < T) (G v : ℝ) :
    Real.sqrt (zetaDivisorBandEdge T G v) =
      Real.sqrt (T / (2 * Real.pi)) * Real.exp (v / G / 2) := by
  rw [zetaDivisorBandEdge, Real.sqrt_mul (by positivity), sqrt_exp_half]

theorem atkinsonRootBand_length_le {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    atkinsonRootBandUpper T G L - atkinsonRootBandLower T G L ≤
      4 * Real.sqrt T * (L / G) := by
  have hu0 : 0 ≤ L / G := by positivity
  have hu : L / G ≤ 1 := (div_le_iff₀ hG).2 (by linarith)
  have hhi := exp_sub_one_le_two_mul hu0 hu
  have hlo := Real.add_one_le_exp (-(L / G))
  have hexp : Real.exp (L / G) - Real.exp (-(L / G)) ≤ 3 * (L / G) := by linarith
  have hA : T / (2 * Real.pi) ≤ T := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hS := Real.sqrt_le_sqrt hA
  rw [atkinsonRootBandUpper, atkinsonRootBandLower, sqrt_zetaDivisorBandEdge hT,
    sqrt_zetaDivisorBandEdge hT, show 2 * L / G / 2 = L / G by ring,
    show -2 * L / G / 2 = -(L / G) by ring, ← mul_sub]
  calc
    _ ≤ Real.sqrt (T / (2 * Real.pi)) * (3 * (L / G)) :=
      mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt T * (3 * (L / G)) := mul_le_mul_of_nonneg_right hS (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (Real.sqrt_nonneg T) hu0]

theorem zetaDivisorBandCutoff_endpoints {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    zetaDivisorBandCutoff T G L (zetaDivisorBandEdge T G (-2 * L)) = 0 ∧
      zetaDivisorBandCutoff T G L (zetaDivisorBandEdge T G (2 * L)) = 0 := by
  have hm := zetaDivisorBandEdge_strictMono hT hG
  exact ⟨zetaBandCutoff_eq_zero_left (hm (by linarith)) le_rfl,
    zetaBandCutoff_eq_zero_right (hm (by linarith)) le_rfl⟩

theorem atkinsonPowerWeight_rootBand_endpoints {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (α : ℝ) :
    atkinsonPowerWeight T G L α (atkinsonRootBandLower T G L ^ 2) = 0 ∧
      atkinsonPowerWeight T G L α (atkinsonRootBandUpper T G L ^ 2) = 0 := by
  have hc := zetaDivisorBandCutoff_endpoints hT hG hL
  have hlo : atkinsonRootBandLower T G L ^ 2 = zetaDivisorBandEdge T G (-2 * L) :=
    Real.sq_sqrt (zetaDivisorBandEdge_pos hT G (-2 * L)).le
  have hhi : atkinsonRootBandUpper T G L ^ 2 = zetaDivisorBandEdge T G (2 * L) :=
    Real.sq_sqrt (zetaDivisorBandEdge_pos hT G (2 * L)).le
  simp only [hlo, hhi, atkinsonPowerWeight, hc.1, hc.2, Complex.ofReal_zero, mul_zero, zero_mul,
    and_self]

theorem exists_intervalC2Bound_atkinsonPowerWeight_root_band (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (fun y => atkinsonPowerWeight T G L α (y ^ 2))
        (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L)
          (C * G * T ^ (-α)) (G / Real.sqrt T) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs := atkinsonRootBand_physical hT (by linarith : 0 < G)
    (by linarith : 0 ≤ L) hwidth
  have hlo : Real.sqrt T / 4 ≤ atkinsonRootBandLower T G L := by
    convert hs.1 using 1
    rw [Real.sqrt_div hT.le]
    norm_num
  exact (hbound T G L hT hG hGT hL hwidth).restrict hlo hs.2

theorem exists_intervalC2Bound_atkinsonSlopeQuotient_band (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L B b : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 6 * Real.sqrt T * (L / G) ≤ B →
      (∀ y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L),
        B ≤ |atkinsonRootSlope T b y|) →
      IntervalC2Bound (fun y => atkinsonPowerWeight T G L α (y ^ 2) *
        (((atkinsonRootSlope T b y)⁻¹ : ℝ) : ℂ))
          (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L)
            (C * G * T ^ (-α) / B) (32 * (G / Real.sqrt T)) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_band α
  refine ⟨12 * C, by positivity, ?_⟩
  intro T G L B b hT hG hGT hL hwidth hB hslope
  have hf := (hbound T G L hT hG hGT hL hwidth).mono le_rfl
    (show G / Real.sqrt T ≤ 32 * (G / Real.sqrt T) by
      have hp : 0 ≤ G / Real.sqrt T := by positivity
      linarith)
  have hi := intervalC2Bound_atkinsonSlope_reciprocal_band hT hG hL hwidth hB b hslope
  convert hf.mul hi using 1
  ring

end MathCollab.Density.Stronger.Atkinson
