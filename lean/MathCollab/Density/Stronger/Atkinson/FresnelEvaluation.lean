module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.FresnelAbelLimit

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fresnel value, branch and explicit finite-window error

The positive real part identifies the principal square root. This yields
both the Cartesian value and its source-facing minus-pi/4 phase.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace MathCollab.Density.Stronger.Atkinson

theorem fresnelGaussianValue_eq_cartesian {c : ℝ} (hc : 0 < c) :
    fresnelGaussianValue c = (1 - I) / ((2 * Real.sqrt c : ℝ) : ℂ) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsC : (Real.sqrt c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : ((1 - I) / ((2 * Real.sqrt c : ℝ) : ℂ)) ^ 2 =
      -I / ((2 * c : ℝ) : ℂ) := by
    push_cast
    field_simp
    rw [← Complex.ofReal_pow, Real.sq_sqrt hc.le]
    ring_nf
    norm_num [Complex.I_sq]
  have hre : 0 < ((1 - I) / ((2 * Real.sqrt c : ℝ) : ℂ)).re := by
    rw [Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.one_re, Complex.I_re, sub_zero]
    positivity
  rw [fresnelGaussianValue, fresnelGaussianBase hc, ← hsq,
    show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by ring]
  exact Complex.sq_cpow_two_inv hre

theorem fresnelGaussianValue_eq_phase {c : ℝ} (hc : 0 < c) :
    fresnelGaussianValue c =
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) / (Real.sqrt (2 * c) : ℂ) := by
  rw [fresnelGaussianValue_eq_cartesian hc, Complex.exp_ofReal_mul_I,
    show -Real.pi / 4 = -(Real.pi / 4) by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : (Real.sqrt c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hc).ne'
  have htwo : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  push_cast
  field_simp
  ring

theorem norm_fresnelGaussianValue {c : ℝ} (hc : 0 < c) :
    ‖fresnelGaussianValue c‖ = 1 / Real.sqrt (2 * c) := by
  rw [fresnelGaussianValue_eq_phase hc, norm_div, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_atkinsonQuadraticWindow_sub_fresnel_le {c H : ℝ}
    (hc : 0 < c) (hH : 0 < H) :
    ‖atkinsonQuadraticWindow c H -
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) / (Real.sqrt (2 * c) : ℂ)‖ ≤
        2 / (c * H * Real.pi) := by
  rw [← fresnelGaussianValue_eq_phase hc]
  exact norm_atkinsonQuadraticWindow_sub_gaussianValue_le hc hH

theorem tendsto_atkinsonQuadraticWindow {c : ℝ} (hc : 0 < c) :
    Tendsto (atkinsonQuadraticWindow c) atTop
      (𝓝 (Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) / (Real.sqrt (2 * c) : ℂ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun H : ℝ => 2 / (c * H * Real.pi)) atTop (𝓝 0) := by
    have h : Tendsto (fun H : ℝ => (2 / (c * Real.pi)) * H⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (2 / (c * Real.pi))
    convert h using 1
    funext H
    ring
  exact squeeze_zero' (Eventually.of_forall (fun H => norm_nonneg _))
    ((eventually_gt_atTop 0).mono fun H hH => norm_atkinsonQuadraticWindow_sub_fresnel_le hc hH) hlim

end MathCollab.Density.Stronger.Atkinson
