module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuous kernels with a bounded primitive

Integration by parts consumes the actual C1 amplitude and the literal
primitive integral. The Fresnel application constructs the primitive bound.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC1Bound.continuousKernel_of_primitive_bound {f K : ℝ → ℂ}
    {a c M B : ℝ} (hf : IntervalC1Bound f a c M)
    (hK : Continuous K) (hac : a ≤ c)
    (hprimitive : ∀ x ∈ Icc a c, ‖∫ y in a..x, K y‖ ≤ B) :
    ‖∫ y in a..c, f y * K y‖ ≤ 2 * B * M := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hprimitive a ⟨le_rfl, hac⟩)
  let F : ℝ → ℂ := fun x => ∫ y in a..x, K y
  have hd (x : ℝ) : HasDerivAt F (K x) x :=
    intervalIntegral.integral_hasDerivAt_right (hK.intervalIntegrable a x)
      hK.stronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hFb (x : ℝ) (hx : x ∈ Icc a c) : ‖F x‖ ≤ B := hprimitive x hx
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := deriv f) (v := F) (v' := K)
    (fun x hx => by
      rw [uIcc_of_le hac] at hx
      exact ((hf.smooth x hx).differentiableAt (by norm_num)).hasDerivAt)
    (fun x _ => hd x) (hf.derivative_integrable hac) (hK.intervalIntegrable a c)
  have hFA : F a = 0 := by simp [F]
  have hvar : ‖∫ y in a..c, deriv f y * F y‖ ≤ B * M := by
    calc
      _ ≤ |∫ y in a..c, ‖deriv f y * F y‖| := intervalIntegral.norm_integral_le_abs_integral_norm
      _ = ∫ y in a..c, ‖deriv f y * F y‖ := by
        rw [abs_of_nonneg (intervalIntegral.integral_nonneg hac (fun _ _ => norm_nonneg _))]
      _ ≤ ∫ y in a..c, ‖deriv f y‖ * B := by
        apply intervalIntegral.integral_mono_on hac
        · simpa only [norm_mul] using
            (hf.derivative_integrable hac).norm.mul_continuousOn hF.norm.continuousOn
        · exact (hf.derivative_integrable hac).norm.mul_const B
        · intro y hy
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hFb y hy) (norm_nonneg _)
      _ = (∫ y in a..c, ‖deriv f y‖) * B := by rw [intervalIntegral.integral_mul_const]
      _ ≤ B * M := by nlinarith [hf.variation_le]
  rw [hparts, hFA, mul_zero, sub_zero]
  apply (norm_sub_le _ _).trans
  have hprod : ‖f c * F c‖ ≤ M * B := by
    rw [norm_mul]
    exact mul_le_mul (hf.norm_le c ⟨hac, le_rfl⟩) (hFb c ⟨hac, le_rfl⟩)
      (norm_nonneg _) hf.nonneg
  linarith

end MathCollab.Density.Stronger.Atkinson
