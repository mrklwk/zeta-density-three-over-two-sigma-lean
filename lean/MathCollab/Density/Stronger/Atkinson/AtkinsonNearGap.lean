module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixGapBound

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# The physical near-height range of the actual prefix gap bound

For a positive dyadic block of length M, gaps at most sqrt(H*M)
satisfy the proved half-period condition throughout [H,2H].
The resulting bound is 60*sqrt(H*M)/|t-u|, for the literal
orientation-free numerical majorant already consumed by the source.
-/

set_option autoImplicit false
noncomputable section

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinson_mul_sqrt_div {H M : ℝ} (hM : 0 < M) :
    M*Real.sqrt (H/M) = Real.sqrt (H*M) := by
  calc
    _ = Real.sqrt (M^2)*Real.sqrt (H/M) := by rw [Real.sqrt_sq hM.le]
    _ = Real.sqrt (M^2*(H/M)) := (Real.sqrt_mul (sq_nonneg M) _).symm
    _ = _ := by congr 1; field_simp

theorem atkinson_near_slope_lower {H u M : ℝ}
    (hH : 0 < H) (hHu : H ≤ u) (hM : 1 ≤ M) :
    Real.sqrt (H/M) ≤ atkinsonIndexSlopeLower u (M+M+1) := by
  have hM0 : 0 < M := by linarith
  have hB : 0 < M+M+1 := by linarith
  unfold atkinsonIndexSlopeLower
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ hM0 hB]
  have hp : 3 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hcoef : M+M+1 ≤ 2*Real.pi*M := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hcoef hH.le
  have h2 := mul_le_mul_of_nonneg_right hHu
    (by positivity : 0 ≤ 2*Real.pi*M)
  nlinarith

theorem atkinson_near_slope_upper {H u M : ℝ}
    (hH : 0 < H) (hu : 0 ≤ u) (huH : u ≤ 2*H) (hM : 0 < M) :
    atkinsonIndexSlopeUpper u M ≤ 10*Real.sqrt (H/M) := by
  have hpi : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hcU : (2*Real.pi+Real.pi^2)*2 ≤ 48 := by nlinarith [Real.pi_lt_four]
  have hn := mul_le_mul hcU huH hu (by norm_num : (0:ℝ) ≤ 48)
  have hrad : (2*Real.pi+Real.pi^2)*(2*u)/M ≤ 100*(H/M) := by
    have hn' : (2*Real.pi+Real.pi^2)*(2*u) ≤ 100*H := by nlinarith
    exact (div_le_div_of_nonneg_right hn' hM.le).trans_eq (by ring)
  unfold atkinsonIndexSlopeUpper
  calc
    _ ≤ Real.sqrt (100*(H/M)) := Real.sqrt_le_sqrt hrad
    _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num

theorem atkinson_near_half_period {H t u : ℝ} {M : ℕ}
    (hH : 0 < H) (hHu : H ≤ u) (hM : 0 < M)
    (hgap : t-u ≤ Real.sqrt (H*(M:ℝ))) :
    atkinsonIndexFirstDerivativeUpper u t M ((M:ℝ)+(M:ℝ)+1) ≤ Real.pi := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hs := atkinson_near_slope_lower hH hHu hM1
  have hscale := mul_le_mul_of_nonneg_left hs hMr.le
  rw [atkinson_mul_sqrt_div hMr] at hscale
  have hden : 0 < (M:ℝ)*atkinsonIndexSlopeLower u ((M:ℝ)+(M:ℝ)+1) :=
    mul_pos hMr (atkinsonIndexSlopeLower_pos (hH.trans_le hHu) (by positivity))
  unfold atkinsonIndexFirstDerivativeUpper
  rw [div_le_iff₀ hden]
  exact mul_le_mul_of_nonneg_left (hgap.trans hscale) Real.pi_nonneg

theorem atkinsonOrderedPrefixGapMajorant_le_near {H t u : ℝ} {M : ℕ}
    (hH : 0 < H) (hHu : H ≤ u) (huH : u ≤ 2*H) (htu : u < t) (hM : 0 < M)
    (hgap : t-u ≤ Real.sqrt (H*(M:ℝ))) :
    atkinsonOrderedPrefixGapMajorant M M t u ≤ 60*Real.sqrt (H*(M:ℝ))/(t-u) := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hu : 0 < u := hH.trans_le hHu
  have hsmall := atkinson_near_half_period hH hHu hM hgap
  have hs := atkinson_near_slope_upper hH hu.le huH hMr
  have hb : 2*((M:ℝ)+(M:ℝ)+1) ≤ 6*(M:ℝ) := by linarith
  have hn := mul_le_mul hb hs (atkinsonIndexSlopeUpper_pos hu hMr).le (by positivity)
  have hn' : 2*((M:ℝ)+(M:ℝ)+1)*atkinsonIndexSlopeUpper u M ≤
      60*Real.sqrt (H*(M:ℝ)) := by
    calc
      _ ≤ 6*(M:ℝ)*(10*Real.sqrt (H/(M:ℝ))) := hn
      _ = 60*((M:ℝ)*Real.sqrt (H/(M:ℝ))) := by ring
      _ = _ := by rw [atkinson_mul_sqrt_div hMr]
  unfold atkinsonOrderedPrefixGapMajorant
  rw [ite_eq_left hsmall]
  apply (min_le_right _ _).trans ((min_le_right _ _).trans _)
  rw [atkinsonPrefixFirstDerivativeMajorant_eq_gap hu htu hM]
  exact div_le_div_of_nonneg_right hn' (sub_pos.mpr htu).le

theorem atkinsonPrefixGapMajorant_le_near {H t u : ℝ} {M : ℕ}
    (hH : 0 < H) (htH : H ≤ t) (hHt : t ≤ 2*H)
    (huH : H ≤ u) (hHu : u ≤ 2*H) (hne : t ≠ u) (hM : 0 < M)
    (hgap : |t-u| ≤ Real.sqrt (H*(M:ℝ))) :
    atkinsonPrefixGapMajorant M M t u ≤ 60*Real.sqrt (H*(M:ℝ))/|t-u| := by
  unfold atkinsonPrefixGapMajorant
  rw [ite_eq_right hne]
  rcases lt_or_gt_of_ne hne with htu | hut
  · rw [max_eq_right htu.le, min_eq_left htu.le, abs_of_neg (sub_neg.mpr htu)] at *
    have hg : u-t ≤ Real.sqrt (H*(M:ℝ)) := by linarith
    simpa only [neg_sub] using
      atkinsonOrderedPrefixGapMajorant_le_near hH htH hHt htu hM hg
  · rw [max_eq_left hut.le, min_eq_right hut.le, abs_of_pos (sub_pos.mpr hut)] at *
    exact atkinsonOrderedPrefixGapMajorant_le_near hH huH hHu hut hM hgap

end MathCollab.Density.Stronger.Atkinson
