module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleSupport
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNaturalAmplitude

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Exact square-root band of the original smooth carrier

Both endpoints are obtained from the existing exponential cutoff.
The integral identity keeps the actual source and its square Jacobian.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonRootBandLower (T G L : ℝ) : ℝ :=
  Real.sqrt (zetaDivisorBandEdge T G (-2 * L))

def atkinsonRootBandUpper (T G L : ℝ) : ℝ :=
  Real.sqrt (zetaDivisorBandEdge T G (2 * L))

theorem atkinsonRootBandLower_pos {T : ℝ} (hT : 0 < T) (G L : ℝ) :
    0 < atkinsonRootBandLower T G L :=
  Real.sqrt_pos.2 (zetaDivisorBandEdge_pos hT G (-2 * L))

theorem atkinsonRootBand_order {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 ≤ L) :
    atkinsonRootBandLower T G L ≤ atkinsonRootBandUpper T G L :=
  Real.sqrt_le_sqrt ((zetaDivisorBandEdge_strictMono hT hG).monotone (by linarith))

theorem atkinsonRootBand_square_mem {T G L y : ℝ} (hT : 0 < T)
    (hy : y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L)) :
    y ^ 2 ∈ Icc (zetaDivisorBandEdge T G (-2 * L)) (zetaDivisorBandEdge T G (2 * L)) := by
  have ha := atkinsonRootBandLower_pos hT G L
  have hb : 0 ≤ atkinsonRootBandUpper T G L := Real.sqrt_nonneg _
  have hsa : (atkinsonRootBandLower T G L) ^ 2 = zetaDivisorBandEdge T G (-2 * L) :=
    Real.sq_sqrt (zetaDivisorBandEdge_pos hT G (-2 * L)).le
  have hsb : (atkinsonRootBandUpper T G L) ^ 2 = zetaDivisorBandEdge T G (2 * L) :=
    Real.sq_sqrt (zetaDivisorBandEdge_pos hT G (2 * L)).le
  constructor <;> nlinarith [hy.1, hy.2]

theorem atkinsonRootBand_physical {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 ≤ L) (hwidth : 8 * L ≤ G) :
    Real.sqrt (T / 16) ≤ atkinsonRootBandLower T G L ∧
      atkinsonRootBandUpper T G L ≤ Real.sqrt T := by
  have h := zetaDivisorBandEdge_outer_bounds hT hG hL hwidth
  constructor
  · apply Real.sqrt_le_sqrt
    apply le_trans _ h.1
    apply div_le_div_of_nonneg_left hT.le (by positivity)
    nlinarith [Real.pi_lt_four]
  · apply Real.sqrt_le_sqrt
    apply h.2.trans
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_three]

theorem zetaAtkinsonSaddle_inverse_root {T y : ℝ} (hT : 0 < T) (hy : 0 < y) :
    zetaAtkinsonSaddle T (y - (T / (2 * Real.pi)) / y) = y ^ 2 := by
  symm
  apply (atkinson_saddle_equation_iff (by positivity : 0 < T / (2 * Real.pi))
    (sq_pos_of_pos hy) _).1
  rw [Real.sqrt_sq hy.le]
  field_simp
  ring

theorem abs_atkinsonRootSlope_zero_le_band {T G L y : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hy : y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L)) :
    |atkinsonRootSlope T 0 y| ≤ 6 * Real.sqrt T * (L / G) := by
  have hy0 := (atkinsonRootBandLower_pos hT G L).trans_le hy.1
  have hlog := zetaDivisorBand_log_bound hT (atkinsonRootBand_square_mem hT hy)
  rw [← zetaAtkinsonSaddle_inverse_root hT hy0] at hlog
  have hb := abs_frequency_le_of_saddle_log_bound hT hG hL hwidth hlog
  have he : atkinsonRootSlope T 0 y = -2 * (y - (T / (2 * Real.pi)) / y) := by
    unfold atkinsonRootSlope
    ring
  rw [he, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  linarith

theorem atkinsonPowerIntegral_eq_root_band {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (α b : ℝ) :
    atkinsonPowerIntegral T G L α b =
      2 * ∫ y in atkinsonRootBandLower T G L..atkinsonRootBandUpper T G L,
        atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y := by
  have hab := atkinsonRootBand_order hT hG hL.le
  have ha := atkinsonRootBandLower_pos hT G L
  have habx := (zetaDivisorBandEdge_strictMono hT hG).monotone
    (show -2 * L ≤ 2 * L by linarith)
  have he : atkinsonPowerIntegral T G L α b =
      ∫ x in zetaDivisorBandEdge T G (-2 * L)..zetaDivisorBandEdge T G (2 * L),
        atkinsonPowerIntegrand T G L α b x := by
    unfold atkinsonPowerIntegral
    rw [intervalIntegral.integral_of_le habx, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => (zetaDivisorBandEdge_pos hT G (-2 * L)).trans_le hx.1)
    intro x hx
    have hz : zetaAtkinsonDivisorTest T G L x = 0 := by
      by_contra hn
      have hs : x ∈ Function.support (zetaSmoothDivisorTest T G L) := by
        rw [← support_zetaAtkinsonDivisorTest]
        exact hn
      exact hx.2 (support_zetaSmoothDivisorTest hT hG hL hs)
    simp [atkinsonPowerIntegrand, hz]
  have hc := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := atkinsonPowerIntegrand T G L α b) (f := fun y : ℝ => y ^ 2)
    (f' := fun y : ℝ => 2 * y)
    (a := atkinsonRootBandLower T G L) (b := atkinsonRootBandUpper T G L)
    (by fun_prop) (fun y _ => by simpa using! (hasDerivAt_id y).pow 2)
    (fun y hy => by
      rw [min_eq_left hab, max_eq_right hab] at hy
      have := ha.trans hy.1
      positivity)
  rw [show (atkinsonRootBandLower T G L) ^ 2 = zetaDivisorBandEdge T G (-2 * L) from
    Real.sq_sqrt (zetaDivisorBandEdge_pos hT G (-2 * L)).le,
    show (atkinsonRootBandUpper T G L) ^ 2 = zetaDivisorBandEdge T G (2 * L) from
    Real.sq_sqrt (zetaDivisorBandEdge_pos hT G (2 * L)).le] at hc
  rw [he, ← hc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hab] at hy
  exact atkinsonPowerIntegrand_sq hT (ha.trans_le hy.1) G L α b

end MathCollab.Density.Stronger.Atkinson
