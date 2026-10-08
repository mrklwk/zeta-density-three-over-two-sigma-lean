module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.QuadraticDivisorShortening
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem exists_logGaussian_power_tail_bound (C p A : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      C * T ^ p * Real.exp (-b * (Real.log T) ^ 2) ≤ T ^ (-A) := by
  let T₀ := max 1 (max C (Real.exp ((A + p + 1) / b)))
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT₀
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT₀
  have hT : 0 < T := by linarith
  have hTC : C ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT₀)
  have hTexp : Real.exp ((A + p + 1) / b) ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hT₀)
  have hlog0 := Real.log_nonneg hT1
  have hlog : (A + p + 1) / b ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hTexp
  have hbLog : A + p + 1 ≤ b * Real.log T := by
    have h := (div_le_iff₀ hb).mp hlog
    linarith
  have hexp : Real.exp (-b * (Real.log T) ^ 2) ≤ T ^ (-(A + p + 1)) := by
    rw [Real.rpow_def_of_pos hT]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hbLog)]
  calc
    _ ≤ T * T ^ p * Real.exp (-b * (Real.log T) ^ 2) := by gcongr
    _ ≤ T * T ^ p * T ^ (-(A + p + 1)) := by gcongr
    _ = T ^ (1 + p) * T ^ (-(A + p + 1)) := by rw [Real.rpow_add hT, Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hT]; congr 1; ring

/-- The real quadratic divisor source is shortened with an arbitrarily
small power tail on the literal cutoff `L=log T`. -/
theorem exists_zetaQuadraticDivisor_log_tail_bound (A : ℝ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      ‖zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G (Real.log T)‖ ≤
        G * T ^ (-A) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaFrozenDivisorQuadraticSum_sub_short_le (1 / 2) (by norm_num)
  obtain ⟨T₀, hT₀, htail⟩ := exists_logGaussian_power_tail_bound C 1 A (b := 1 / 8) (by norm_num)
  refine ⟨T₀, hT₀, ?_⟩
  intro T G hT hG hGT
  have hT1 := hT₀.trans hT
  have h := hbound T G (Real.log T) hT1 hG hGT (Real.log_nonneg hT1)
  have he := mul_le_mul_of_nonneg_left (htail T hT) hG.le
  rw [Real.rpow_one] at he
  norm_num only [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at h
  apply h.trans
  rw [show -(Real.log T) ^ 2 / 8 = -(1 / 8) * (Real.log T) ^ 2 by ring]
  calc
    _ = G * (C * T * Real.exp (-(1 / 8) * (Real.log T) ^ 2)) := by ring
    _ ≤ _ := he

theorem eventually_const_log_pow_le_rpow (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, C * (Real.log T) ^ k ≤ T ^ η := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hη).const_mul_left C
  filter_upwards [hsmall.bound (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with T h hT
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (mul_nonneg hC (pow_nonneg (Real.log_nonneg hT) k)),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) η)] using h

theorem gaussian_width_sq_le_height {T G δ : ℝ} (hT : 1 ≤ T) (hG : 0 ≤ G)
    (hδ : 0 ≤ δ) (hwidth : G ≤ T ^ (1 / 2 - δ)) : G ^ 2 ≤ T := by
  have hT0 : 0 < T := by linarith
  calc
    _ ≤ (T ^ (1 / 2 - δ)) ^ 2 := pow_le_pow_left₀ hG hwidth 2
    _ = T ^ ((1 / 2 - δ) * 2) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
    _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    _ = T := Real.rpow_one T

/-- The physical window and quadratic scale are derived, not additional
assumptions after choosing a sub-square-root Gaussian width. -/
theorem eventually_zeta_source_log_window_scales {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, 8 ≤ T ∧ 1 ≤ Real.log T ∧
      ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - δ) →
        G ^ 2 ≤ 2 * T ∧ G * Real.log T ≤ T / 2 ∧ G ≤ T := by
  filter_upwards [eventually_const_log_pow_le_rpow 2 (by norm_num) 1 (η := δ / 2) (by positivity),
    eventually_ge_atTop (8 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hlog hT hlog1
  refine ⟨hT, hlog1, ?_⟩
  intro G hG hwidth
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hsq := gaussian_width_sq_le_height hT1 hG.le hδ.le hwidth
  have hGpow : G ≤ T := hwidth.trans (by
    calc
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = _ := Real.rpow_one T)
  refine ⟨by linarith, ?_, hGpow⟩
  simp only [pow_one] at hlog
  have hprod : 2 * (G * Real.log T) ≤ T ^ (1 / 2 - δ + δ / 2) := by
    rw [Real.rpow_add hT0]
    calc
      _ = G * (2 * Real.log T) := by ring
      _ ≤ T ^ (1 / 2 - δ) * T ^ (δ / 2) :=
        mul_le_mul hwidth hlog (by linarith) (Real.rpow_nonneg hT0.le _)
  have hpow : T ^ (1 / 2 - δ + δ / 2) ≤ T := by
    calc
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = _ := Real.rpow_one T
  linarith

end MathCollab.Density.Stronger.Atkinson
