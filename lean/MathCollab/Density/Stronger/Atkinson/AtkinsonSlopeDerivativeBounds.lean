module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSecondOrderIntegration

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Physical first and second derivatives of the phase slope

The reciprocal phase slope has the same natural derivative scale as the
source amplitude once the frequency is outside the exact smooth band.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Filter Set
open scoped Topology ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC2Bound.restrict {f : ℝ → ℂ} {a c u v M R : ℝ}
    (hf : IntervalC2Bound f a c M R) (hau : a ≤ u) (hvc : v ≤ c) :
    IntervalC2Bound f u v M R := by
  have hmem {x : ℝ} (hx : x ∈ Icc u v) : x ∈ Icc a c :=
    ⟨hau.trans hx.1, hx.2.trans hvc⟩
  exact ⟨hf.nonneg, hf.scale_nonneg, fun x hx => hf.smooth x (hmem hx),
    fun x hx => hf.norm_le x (hmem hx), fun x hx => hf.deriv_le x (hmem hx),
    fun x hx => hf.second_le x (hmem hx)⟩

theorem hasDerivAt_atkinsonRootSlopeFirst (T : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => -T / (Real.pi * z ^ 2) - 2)
      (2 * T / (Real.pi * y ^ 3)) y := by
  have h := ((((hasDerivAt_id y).pow 2).inv (pow_ne_zero 2 hy.ne')).const_mul
    (-T / Real.pi)).sub_const 2
  convert h using 1
  · funext z
    dsimp
    ring
  · dsimp
    field_simp

theorem iteratedDeriv_two_atkinsonRootSlope (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 2 (atkinsonRootSlope T b) y = 2 * T / (Real.pi * y ^ 3) := by
  have he : deriv (atkinsonRootSlope T b) =ᶠ[𝓝 y]
      fun z => -T / (Real.pi * z ^ 2) - 2 := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact (hasDerivAt_atkinsonRootSlope T b hz).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  exact (hasDerivAt_atkinsonRootSlopeFirst T hy).deriv

theorem atkinsonRootSlope_derivative_bounds {T y : ℝ} (hT : 0 < T)
    (hy : Real.sqrt T / 4 ≤ y) (b : ℝ) :
    |deriv (atkinsonRootSlope T b) y| ≤ 8 ∧
      |iteratedDeriv 2 (atkinsonRootSlope T b) y| ≤ 64 / Real.sqrt T := by
  have hS : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hy0 : 0 < y := by linarith
  have hT16 : T ≤ 16 * y ^ 2 := by nlinarith [Real.sq_sqrt hT.le]
  have hfrac : T / (Real.pi * y ^ 2) ≤ 6 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi * y ^ 2)).2
    nlinarith [mul_nonneg (show 0 ≤ 6 * Real.pi - 16 by linarith [Real.pi_gt_three]) (sq_nonneg y)]
  constructor
  · rw [(hasDerivAt_atkinsonRootSlope T b hy0).deriv,
      abs_of_nonpos (by
        have hp : 0 ≤ T / (Real.pi * y ^ 2) := by positivity
        rw [neg_div]
        linarith)]
    rw [neg_div]
    linarith
  · rw [iteratedDeriv_two_atkinsonRootSlope T b hy0,
      abs_of_pos (by positivity : 0 < 2 * T / (Real.pi * y ^ 3))]
    apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * y ^ 3) hS).2
    have h1 := mul_le_mul_of_nonneg_right hT16 hS.le
    have h2 := mul_le_mul_of_nonneg_left (show Real.sqrt T ≤ 4 * y by linarith)
      (show 0 ≤ 16 * y ^ 2 by positivity)
    nlinarith [mul_nonneg (show 0 ≤ 64 * Real.pi - 128 by linarith [Real.pi_gt_three])
      (show 0 ≤ y ^ 3 by positivity)]

theorem intervalC2Bound_atkinsonSlope_reciprocal_band {T G L B : ℝ}
    (hT : 0 < T) (hG : 1 ≤ G) (hL : 1 ≤ L) (hwidth : 8 * L ≤ G)
    (hB : 6 * Real.sqrt T * (L / G) ≤ B) (b : ℝ)
    (hslope : ∀ y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L),
      B ≤ |atkinsonRootSlope T b y|) :
    IntervalC2Bound (fun y => (((atkinsonRootSlope T b y)⁻¹ : ℝ) : ℂ))
      (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L)
        (3 / B) (32 * (G / Real.sqrt T)) := by
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hS : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hB0 : 0 < B := (by positivity : 0 < 6 * Real.sqrt T * (L / G)).trans_le hB
  have hBG : 6 * L ≤ B * (G / Real.sqrt T) := by
    calc
      _ = (6 * Real.sqrt T * (L / G)) * (G / Real.sqrt T) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hB (by positivity)
  have hBGR : 6 ≤ (B * (G / Real.sqrt T)) * G := by
    have h := mul_le_mul_of_nonneg_right hBG hG0.le
    nlinarith
  have hmem (y : ℝ)
      (hy : y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L)) :
      Real.sqrt T / 4 ≤ y := by
    have h := (atkinsonRootBand_physical hT hG0 hL0.le hwidth).1.trans hy.1
    rw [Real.sqrt_div hT.le] at h
    norm_num at h
    exact h
  refine intervalC2Bound_real_reciprocal hB0 (by positivity) ?_ hslope ?_ ?_
  · intro y hy
    have hy0 := (atkinsonRootBandLower_pos hT G L).trans_le hy.1
    unfold atkinsonRootSlope
    fun_prop (disch := positivity)
  · intro y hy
    apply (atkinsonRootSlope_derivative_bounds hT (hmem y hy) b).1.trans
    nlinarith
  · intro y hy
    apply (atkinsonRootSlope_derivative_bounds hT (hmem y hy) b).2.trans
    calc
      _ ≤ (1024 * (B * (G / Real.sqrt T)) * G) / Real.sqrt T := by
        apply div_le_div_of_nonneg_right _ hS.le
        nlinarith
      _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
