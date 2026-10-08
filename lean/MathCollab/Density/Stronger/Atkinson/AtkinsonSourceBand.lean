module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSharpTruncation
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Physical zeta source with source-scale leading truncation

The actual Gaussian and local-mean theorems now require only a cutoff
N >= 36 T (log(T)/G)^2. The retained carriers have not been replaced by
a sum of stationary approximations with an assumed summed error.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Filter MeasureTheory

namespace MathCollab.Density.Stronger.Atkinson

theorem exists_atkinsonLeading_source_band_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      ‖atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N‖ ≤
        C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonLeadingSum_sub_band_finite_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      ‖atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N‖ ≤
        (2 * C) * G := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ,
      eventually_const_log_pow_le_rpow 1 (by norm_num) 1 (η := 1 / 4) (by norm_num)] with
      T hsupport hscale hlog
    intro G hlower hupper N hN
    obtain ⟨hG0, hlog0, hwidth, _⟩ := hsupport.2 G hlower
    have hT : 1 ≤ T := by linarith [hsupport.1]
    have hG : 1 ≤ G := (Real.one_le_rpow hT hδ.le).trans hlower
    have hGT := (hscale.2.2 G hG0 hupper).1
    apply (hbound T G (Real.log T) hT hG hGT hscale.2.1 hwidth N hN).trans
    have h := mul_le_mul_of_nonneg_left
      (atkinsonBand_tail_scale_le hT hG0.le hGT hlog0.le
        (by simpa only [one_mul, pow_one] using hlog)) hC.le
    convert h using 1 <;> ring
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨2 * C, by positivity, max 16 B, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper N hN
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper N hN

end MathCollab.Density.Stronger.Atkinson
