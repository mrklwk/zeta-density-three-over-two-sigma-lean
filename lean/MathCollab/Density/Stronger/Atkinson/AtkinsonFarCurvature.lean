module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNearGap

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Physical curvature scales for far-height cancellation

The two additional discrete mean-value endpoints give B=2M+2 <= 4M.
The actual curvature scales are bounded in terms of Q=M*sqrt(H*M).
-/

set_option autoImplicit false
noncomputable section

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinson_far_slope_lower {H u M B : ℝ}
    (hH : 0 < H) (hHu : H ≤ u) (hM : 0 < M) (hB : 0 < B) (hBM : B ≤ 4*M) :
    Real.sqrt (H/M) ≤ atkinsonIndexSlopeLower u B := by
  unfold atkinsonIndexSlopeLower
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ hM hB]
  have hcoef : B ≤ 2*Real.pi*M := by nlinarith [Real.pi_gt_three]
  have h1 := mul_le_mul_of_nonneg_left hcoef hH.le
  have h2 := mul_le_mul_of_nonneg_right hHu
    (by positivity : 0 ≤ 2*Real.pi*M)
  nlinarith

theorem atkinson_far_box_curvature_bounds {H u M B : ℝ}
    (hH : 0 < H) (hHu : H ≤ u) (huH : u ≤ 2*H)
    (hM : 0 < M) (hB : 0 < B) (hBM : B ≤ 4*M) :
    1/(320*(M*Real.sqrt (H*M))) ≤ atkinsonIndexBoxCurvatureLower u M B ∧
      atkinsonIndexBoxCurvatureUpper u M B ≤ 4/(M*Real.sqrt (H*M)) := by
  have hu : 0 < u := hH.trans_le hHu
  have hsU := atkinson_near_slope_upper hH hu.le huH hM
  have hsL := atkinson_far_slope_lower hH hHu hM hB hBM
  have hQ : 0 < M*Real.sqrt (H*M) := by positivity
  have hDL : 0 < 2*B^2*atkinsonIndexSlopeUpper u M :=
    mul_pos (by positivity) (atkinsonIndexSlopeUpper_pos hu hM)
  have hDU : 0 < M^2*atkinsonIndexSlopeLower u B :=
    mul_pos (by positivity) (atkinsonIndexSlopeLower_pos hu hB)
  have hBsq : B^2 ≤ (4*M)^2 := pow_le_pow_left₀ hB.le hBM 2
  have hdenL : 2*B^2*atkinsonIndexSlopeUpper u M ≤ 320*(M*Real.sqrt (H*M)) := by
    calc
      _ ≤ 2*(4*M)^2*(10*Real.sqrt (H/M)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hBsq (by norm_num)) hsU
          (atkinsonIndexSlopeUpper_pos hu hM).le (by positivity)
      _ = 320*(M*(M*Real.sqrt (H/M))) := by ring
      _ = _ := by rw [atkinson_mul_sqrt_div hM]
  have hdenU : M*Real.sqrt (H*M) ≤ M^2*atkinsonIndexSlopeLower u B := by
    calc
      _ = M^2*Real.sqrt (H/M) := by rw [← atkinson_mul_sqrt_div hM]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsL (sq_nonneg M)
  constructor
  · unfold atkinsonIndexBoxCurvatureLower
    rw [div_le_div_iff₀ (by positivity : 0 < 320*(M*Real.sqrt (H*M))) hDL]
    have hp := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
      (by positivity : 0 ≤ 320*(M*Real.sqrt (H*M)))
    nlinarith
  · unfold atkinsonIndexBoxCurvatureUpper
    rw [div_le_div_iff₀ hDU hQ]
    have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hQ.le
    nlinarith

theorem atkinson_far_lambda_bounds {H t u : ℝ} {M : ℕ}
    (hH : 0 < H) (hHu : H ≤ u) (huH : u ≤ 2*H) (htu : u < t) (hM : 0 < M) :
    (t-u)/(320*((M:ℝ)*Real.sqrt (H*(M:ℝ)))) ≤ atkinsonIndexBProcessLambda t u M M ∧
      atkinsonIndexBProcessLambdaUpper t u M M ≤ 4*(t-u)/((M:ℝ)*Real.sqrt (H*(M:ℝ))) := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hB : (0:ℝ) < (M:ℝ)+(M:ℝ)+2 := by positivity
  have hBM : (M:ℝ)+(M:ℝ)+2 ≤ 4*(M:ℝ) := by linarith
  have hb := atkinson_far_box_curvature_bounds hH hHu huH hMr hB hBM
  unfold atkinsonIndexBProcessLambda atkinsonIndexBProcessLambdaUpper
  constructor
  · exact (show (t-u)/(320*((M:ℝ)*Real.sqrt (H*(M:ℝ)))) =
      (1/(320*((M:ℝ)*Real.sqrt (H*(M:ℝ)))))*(t-u) by ring).trans_le
        (mul_le_mul_of_nonneg_right hb.1 (sub_pos.mpr htu).le)
  · exact (mul_le_mul_of_nonneg_right hb.2 (sub_pos.mpr htu).le).trans_eq (by ring)

end MathCollab.Density.Stronger.Atkinson
