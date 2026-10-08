module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.SourceLogScales

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


theorem source_log_monomial_le_one {T G δ : ℝ} (hT : 1 ≤ T)
    (hδ : 0 < δ) (hwidth : G ≤ T ^ (1 / 2 - δ)) (hlog : 1 ≤ Real.log T)
    (hlog4 : (Real.log T) ^ 4 ≤ T ^ (δ / 2)) {k : ℕ} (hk : k ≤ 4) :
    G * (Real.log T) ^ k * T ^ (-1 / 2 + δ / 4) ≤ 1 := by
  have hT0 : 0 < T := by linarith
  have hlogk := (pow_le_pow_right₀ hlog hk).trans hlog4
  calc
    _ ≤ (T ^ (1 / 2 - δ) * T ^ (δ / 2)) * T ^ (-1 / 2 + δ / 4) := by gcongr
    _ = T ^ ((1 / 2 - δ + δ / 2) + (-1 / 2 + δ / 4)) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
    _ ≤ T ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    _ = _ := Real.rpow_zero T

theorem source_scaled_window_square_le {T G δ : ℝ} (hT : 1 ≤ T) (hG : 0 ≤ G)
    (hδ : 0 < δ) (hwidth : G ≤ T ^ (1 / 2 - δ)) (hlog : 1 ≤ Real.log T)
    (hlog4 : (Real.log T) ^ 4 ≤ T ^ (δ / 2)) :
    T ^ (1 / 2 + δ / 4) * (G * Real.log T) ^ 2 / T ≤ G := by
  have hT0 : 0 < T := by linarith
  have h := mul_le_mul_of_nonneg_left
    (source_log_monomial_le_one hT hδ hwidth hlog hlog4 (k := 2) (by norm_num)) hG
  have hp : T ^ (-1 / 2 + δ / 4) = T ^ (1 / 2 + δ / 4) / T := by
    rw [show (-1 / 2 + δ / 4) = (1 / 2 + δ / 4) - 1 by ring,
      Real.rpow_sub_one hT0.ne']
  rw [hp, mul_one] at h
  convert h using 1
  ring

theorem source_window_square_le_height {T G δ : ℝ} (hT : 1 ≤ T) (hG : 0 ≤ G)
    (hδ : 0 < δ) (hwidth : G ≤ T ^ (1 / 2 - δ)) (hlog : 1 ≤ Real.log T)
    (hlog4 : (Real.log T) ^ 4 ≤ T ^ (δ / 2)) : (G * Real.log T) ^ 2 ≤ T := by
  have hT0 : 0 < T := by linarith
  have hsq := (div_le_iff₀ hT0).mp (source_scaled_window_square_le hT hG hδ hwidth hlog hlog4)
  have hGpow : G ≤ T ^ (1 / 2 + δ / 4) :=
    hwidth.trans (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
  have hprod := mul_le_mul_of_nonneg_right hGpow hT0.le
  nlinarith [Real.rpow_pos_of_pos hT0 (1 / 2 + δ / 4)]

theorem source_scaled_window_fourth_le {T G δ : ℝ} (hT : 1 ≤ T) (hG : 0 ≤ G)
    (hδ : 0 < δ) (hwidth : G ≤ T ^ (1 / 2 - δ)) (hlog : 1 ≤ Real.log T)
    (hlog4 : (Real.log T) ^ 4 ≤ T ^ (δ / 2)) :
    T ^ (1 / 2 + δ / 4) * (G * Real.log T) ^ 4 / T ^ 2 ≤ G := by
  have hT0 : 0 < T := by linarith
  have hratio : (G * Real.log T) ^ 2 / T ≤ 1 :=
    (div_le_one hT0).mpr (source_window_square_le_height hT hG hδ hwidth hlog hlog4)
  calc
    _ = (T ^ (1 / 2 + δ / 4) * (G * Real.log T) ^ 2 / T) *
        ((G * Real.log T) ^ 2 / T) := by ring
    _ ≤ G * 1 := mul_le_mul (source_scaled_window_square_le hT hG hδ hwidth hlog hlog4)
      hratio (by positivity) hG
    _ = _ := mul_one G

theorem source_scaled_quadratic_phase_error_le {T G δ : ℝ} (hT : 1 ≤ T) (hG : 0 ≤ G)
    (hδ : 0 < δ) (hwidth : G ≤ T ^ (1 / 2 - δ)) (hlog : 1 ≤ Real.log T)
    (hlog4 : (Real.log T) ^ 4 ≤ T ^ (δ / 2)) :
    T ^ (1 / 2 + δ / 4) *
      (4 * (G * Real.log T) ^ 2 * (18 / T + 2 * (G * Real.log T) ^ 2 / T ^ 2)) ≤ 80 * G := by
  have h2 := source_scaled_window_square_le hT hG hδ hwidth hlog hlog4
  have h4 := source_scaled_window_fourth_le hT hG hδ hwidth hlog hlog4
  calc
    _ = 72 * (T ^ (1 / 2 + δ / 4) * (G * Real.log T) ^ 2 / T) +
        8 * (T ^ (1 / 2 + δ / 4) * (G * Real.log T) ^ 4 / T ^ 2) := by ring
    _ ≤ _ := by linarith

/-- On every sub-square-root width, the actual Gaussian zeta window is
the complete quadratic divisor source up to `Oδ(G log T)`. -/
theorem exists_zetaSquareGaussianWindow_log_error {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |zetaSquareGaussianWindow T G (Real.log T) - 2 * (zetaFrozenDivisorQuadraticSum T G).re| ≤
        C * G * Real.log T := by
  obtain ⟨C, hC, hsource⟩ := exists_abs_zetaSquareGaussianWindow_sub_quadratic_le (δ / 4) (by positivity)
  obtain ⟨D, hD, hmass⟩ := exists_tsum_norm_source_divisor_weight_le (δ / 4) (by positivity)
  obtain ⟨B, hB, htail⟩ := exists_logGaussian_power_tail_bound
    (6 * D * Real.sqrt (2 * Real.pi)) (1 / 2 + δ / 4) 0 (b := 1 / 2) (by norm_num)
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |zetaSquareGaussianWindow T G (Real.log T) - 2 * (zetaFrozenDivisorQuadraticSum T G).re| ≤
        (2 * C + 80 * D + 1) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ,
      eventually_const_log_pow_le_rpow 1 (by norm_num) 4 (η := δ / 2) (by positivity),
      eventually_ge_atTop B] with T hscale hlog4 hTB
    intro G hG hwidth
    have hT := hscale.1
    have hlog := hscale.2.1
    obtain ⟨hGT, hrT, _⟩ := hscale.2.2 G hG hwidth
    have hT1 : 1 ≤ T := by linarith
    have hT0 : 0 < T := by linarith
    simp only [one_mul] at hlog4
    let M : ℝ := ∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖
    have hM : M ≤ D * T ^ (1 / 2 + δ / 4) := by
      simpa only [M, zetaFrozenDivisorCoefficient, norm_mul] using hmass T hT1 (-T)
    have hr0 : 0 ≤ G * Real.log T := by positivity
    have hmain := hsource T G (G * Real.log T) hT hG hGT hr0 hrT
    rw [mul_div_cancel_left₀ _ hG.ne'] at hmain
    have hfreeze : C * (G * Real.log T) * (1 + G * Real.log T * T ^ (-1 / 2 + δ / 4)) ≤
        2 * C * G * Real.log T := by
      have h := source_log_monomial_le_one hT1 hδ hwidth hlog hlog4 (k := 1) (by norm_num)
      simp only [pow_one] at h
      have hm := mul_le_mul_of_nonneg_left (show 1 + G * Real.log T * T ^ (-1 / 2 + δ / 4) ≤ 2 by linarith)
        (show 0 ≤ C * (G * Real.log T) by positivity)
      convert hm using 1
      ring
    have hphase : M * (4 * (G * Real.log T) ^ 2 *
        (18 / T + 2 * (G * Real.log T) ^ 2 / T ^ 2)) ≤ 80 * D * G := by
      calc
        _ ≤ (D * T ^ (1 / 2 + δ / 4)) * (4 * (G * Real.log T) ^ 2 *
            (18 / T + 2 * (G * Real.log T) ^ 2 / T ^ 2)) := mul_le_mul_of_nonneg_right hM (by positivity)
        _ = D * (T ^ (1 / 2 + δ / 4) * (4 * (G * Real.log T) ^ 2 *
            (18 / T + 2 * (G * Real.log T) ^ 2 / T ^ 2))) := by ring
        _ ≤ D * (80 * G) := mul_le_mul_of_nonneg_left
          (source_scaled_quadratic_phase_error_le hT1 hG.le hδ hwidth hlog hlog4) hD.le
        _ = _ := by ring
    have hgauss : M * (6 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(Real.log T) ^ 2 / 2)) ≤ G := by
      have ht := htail T hTB
      simp only [neg_zero, Real.rpow_zero] at ht
      calc
        _ ≤ (D * T ^ (1 / 2 + δ / 4)) *
            (6 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(Real.log T) ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
        _ = G * ((6 * D * Real.sqrt (2 * Real.pi)) * T ^ (1 / 2 + δ / 4) *
            Real.exp (-(1 / 2) * (Real.log T) ^ 2)) := by
          rw [show -(Real.log T) ^ 2 / 2 = -(1 / 2) * (Real.log T) ^ 2 by ring]
          ring
        _ ≤ G * 1 := mul_le_mul_of_nonneg_left ht hG.le
        _ = G := mul_one G
    have hGlog : G ≤ G * Real.log T := by nlinarith
    change _ ≤ C * (G * Real.log T) * _ + M * _ at hmain
    nlinarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨2 * C + 80 * D + 1, by positivity, max 8 T₁, le_max_left _ _, ?_⟩
  intro T G hT hG hwidth
  exact hT₁ T ((le_max_right _ _).trans hT) G hG hwidth

end MathCollab.Density.Stronger.Atkinson
