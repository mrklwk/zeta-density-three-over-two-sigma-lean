module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleGaussianIdentities
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryMain
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPhysicalCutoff

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem log_zetaDivisorBandEdge {T : ℝ} (hT : 0 < T) (G v : ℝ) :
    Real.log (zetaDivisorBandEdge T G v) = Real.log (T / (2 * Real.pi)) + v / G := by
  rw [zetaDivisorBandEdge, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]

theorem zetaDivisorBand_log_bound {T G L x : ℝ} (hT : 0 < T)
    (hs : x ∈ Icc (zetaDivisorBandEdge T G (-2 * L)) (zetaDivisorBandEdge T G (2 * L))) :
    |Real.log x - Real.log (T / (2 * Real.pi))| ≤ 2 * L / G := by
  have hlo := Real.log_le_log (zetaDivisorBandEdge_pos hT G (-2 * L)) hs.1
  have hxp := (zetaDivisorBandEdge_pos hT G (-2 * L)).trans_le hs.1
  have hhi := Real.log_le_log hxp hs.2
  rw [log_zetaDivisorBandEdge hT] at hlo hhi
  rw [show -2 * L / G = -(2 * L / G) by ring] at hlo
  apply abs_le.mpr
  constructor <;> linarith

theorem zetaDivisorBandCutoff_log_bound {T G L x : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L)
    (hx : zetaDivisorBandCutoff T G L x ≠ 0) :
    |Real.log x - Real.log (T / (2 * Real.pi))| ≤ 2 * L / G :=
  zetaDivisorBand_log_bound hT (support_zetaDivisorBandCutoff hT hG hL hx)

theorem arsinh_abs (x : ℝ) : Real.arsinh |x| = |Real.arsinh x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (Real.arsinh_nonneg_iff.mpr hx)]
  · rw [abs_of_nonpos hx, Real.arsinh_neg,
      abs_of_nonpos (Real.arsinh_nonpos_iff.mpr hx)]

theorem abs_le_three_mul_of_arsinh_bound {x a : ℝ} (ha : a ≤ 1 / 8)
    (hx : |Real.arsinh x| ≤ a) : |x| ≤ 3 * a := by
  have htwo : |x| ≤ 2 := by
    by_contra h
    have hm := Real.arsinh_strictMono (lt_of_not_ge h)
    rw [arsinh_abs] at hm
    have hl := third_mul_le_arsinh (x := 2) (by norm_num) le_rfl
    linarith
  have hl := third_mul_le_arsinh (abs_nonneg x) htwo
  rw [arsinh_abs] at hl
  linarith

theorem abs_frequency_le_of_saddle_log_bound {T G L b : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hlog : |Real.log (zetaAtkinsonSaddle T b) - Real.log (T / (2 * Real.pi))| ≤ 2 * L / G) :
    |b| ≤ 3 * Real.sqrt T * (L / G) := by
  rw [zetaAtkinsonSaddle_log_argument hT, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hlog
  rw [mul_div_assoc] at hlog
  have ha : L / G ≤ 1 / 8 := (div_le_iff₀ hG).2 (by linarith)
  have hx := abs_le_three_mul_of_arsinh_bound ha
    (show |Real.arsinh (b / (2 * Real.sqrt (T / (2 * Real.pi))))| ≤ L / G by linarith)
  have hA : 0 < T / (2 * Real.pi) := by positivity
  have hS : 0 < Real.sqrt (T / (2 * Real.pi)) := Real.sqrt_pos.2 hA
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (T / (2 * Real.pi)))] at hx
  have hbnd := (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (T / (2 * Real.pi)))).mp hx
  have hsqrt : 2 * Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt hA.le
    have hTval : 4 * (T / (2 * Real.pi)) ≤ T := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [Real.pi_gt_three]
    nlinarith [Real.sq_sqrt hT.le, Real.sqrt_nonneg T]
  have hmul := mul_le_mul_of_nonneg_right hsqrt (by positivity : 0 ≤ 3 * (L / G))
  nlinarith

theorem abs_frequency_le_of_saddle_cutoff {T G L b : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hb : zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) ≠ 0) :
    |b| ≤ 3 * Real.sqrt T * (L / G) :=
  abs_frequency_le_of_saddle_log_bound hT hG hL hwidth
    (zetaDivisorBandCutoff_log_bound hT hG hL hb)

theorem atkinsonStationaryMain_eq_zero_of_frequency {T G L b : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hb : 3 * Real.sqrt T * (L / G) < |b|) (α : ℝ) :
    atkinsonStationaryMain T G L α b = 0 := by
  have hc : zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) = 0 := by
    by_contra h
    exact (not_lt_of_ge (abs_frequency_le_of_saddle_cutoff hT hG hL hwidth h)) hb
  change zetaDivisorBandCutoff T G L ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) = 0 at hc
  simp only [atkinsonStationaryMain, atkinsonPowerWeight, hc, Complex.ofReal_zero, mul_zero, zero_mul]

theorem atkinsonStationaryMain_pair_eq_zero_of_index {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (α : ℝ) (n : ℕ) (hn : 9 * T * (L / G) ^ 2 < (n : ℝ)) :
    atkinsonStationaryMain T G L α (Real.sqrt n) = 0 ∧
      atkinsonStationaryMain T G L α (-Real.sqrt n) = 0 := by
  have hb : 3 * Real.sqrt T * (L / G) < |Real.sqrt (n : ℝ)| := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : (3 * Real.sqrt T * (L / G)) ^ 2 = 9 * T * (L / G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]
      ring
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n), Real.sqrt_nonneg (n : ℝ),
      show 0 ≤ 3 * Real.sqrt T * (L / G) by positivity]
  exact ⟨atkinsonStationaryMain_eq_zero_of_frequency hT hG hL hwidth hb α,
    atkinsonStationaryMain_eq_zero_of_frequency hT hG hL hwidth (by simpa only [abs_neg]) α⟩

theorem atkinsonStationaryMain_pair_eq_zero_after_cutoff {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (α : ℝ) (n : ℕ) (hn : atkinsonSourceCutoff T G L ≤ n) :
    atkinsonStationaryMain T G L α (Real.sqrt n) = 0 ∧
      atkinsonStationaryMain T G L α (-Real.sqrt n) = 0 := by
  apply atkinsonStationaryMain_pair_eq_zero_of_index hT hG hL hwidth α n
  have h : 36 * T * (L / G) ^ 2 ≤ (n : ℝ) :=
    (atkinsonSourceCutoff_lower T G L).trans (by exact_mod_cast hn)
  have hp : 0 < T * (L / G) ^ 2 := by positivity
  nlinarith

end MathCollab.Density.Stronger.Atkinson
