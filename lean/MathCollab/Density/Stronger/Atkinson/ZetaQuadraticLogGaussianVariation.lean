module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaLogGaussianVariation
public import MathCollab.Density.Stronger.Atkinson.DivisorTestSmooth

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform variation of the actual logarithmic quadratic Gaussian

The derivative is majorized by the derivative of its real Gaussian
envelope. The latter has total variation at most two. This retains
the full complex quadratic coefficient and saves the otherwise lost
factor of the source width.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem deriv_zetaQuadraticLogGaussian (T A : ℝ) {G x : ℝ} (hG : G ≠ 0) (hx : 0 < x) :
    deriv (fun y => zetaGaussianQuadraticIntegral T G (Real.log y - Real.log A)) x =
      (1 / x : ℝ) • deriv (zetaGaussianQuadraticIntegral T G) (Real.log x - Real.log A) := by
  have hq := (hasDerivAt_zetaGaussianQuadraticIntegral T hG (Real.log x - Real.log A)).differentiableAt
  simpa only [one_div] using!
    (hq.hasDerivAt.scomp x ((Real.hasDerivAt_log hx.ne').sub_const (Real.log A))).deriv

theorem norm_deriv_zetaQuadraticLogGaussian_le {T G x : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hx : 0 < x) (A : ℝ) :
    ‖deriv (fun y => zetaGaussianQuadraticIntegral T G (Real.log y - Real.log A)) x‖ ≤
      (2 * Real.sqrt Real.pi * G) *
        ‖deriv (fun y : ℝ => (zetaLogGaussianEnvelope A G y : ℂ)) x‖ := by
  have he : deriv (fun y : ℝ => (zetaLogGaussianEnvelope A G y : ℂ)) x =
      ((-(G ^ 2 / 4) * ((Real.log x - Real.log A) / x) * zetaLogGaussianEnvelope A G x : ℝ) : ℂ) :=
    (hasDerivAt_zetaLogGaussianEnvelope A G hx).ofReal_comp.deriv
  have habs : |-(G ^ 2 / 4) * ((Real.log x - Real.log A) / x) * zetaLogGaussianEnvelope A G x| =
      (G ^ 2 / 4) * (|Real.log x - Real.log A| / x) * zetaLogGaussianEnvelope A G x := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ G ^ 2 / 4),
      abs_div, abs_of_pos hx, abs_of_nonneg (zetaLogGaussianEnvelope_bounds A G x).1]
  rw [deriv_zetaQuadraticLogGaussian T A hG.ne' hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / x)]
  calc
    _ ≤ (1 / x) * ((Real.sqrt Real.pi * G ^ 3 / 2) * |Real.log x - Real.log A| *
        Real.exp (-(G * (Real.log x - Real.log A)) ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left (norm_deriv_zetaGaussianQuadraticIntegral_le hT hG hGT _)
        (by positivity)
    _ = _ := by
      rw [he, Complex.norm_real, Real.norm_eq_abs, habs]
      unfold zetaLogGaussianEnvelope
      ring

theorem intervalC1Bound_zetaQuadraticLogGaussian {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) :
    IntervalC1Bound
      (fun x => zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi))))
      (T / 16) T (4 * Real.sqrt Real.pi * G) := by
  let A : ℝ := T / (2 * Real.pi)
  have hcenter := atkinson_center_mem_physical hT
  have henv := intervalC1Bound_zetaLogGaussianEnvelope (by positivity : 0 < T / 16)
    hcenter.1 hcenter.2 G
  have hinterval : T / 16 ≤ T := by linarith
  have hs (x : ℝ) (hx : x ∈ Icc (T / 16) T) :
      ContDiffAt ℝ 1 (fun y => zetaGaussianQuadraticIntegral T G (Real.log y - Real.log A)) x := by
    have hl : ContDiffAt ℝ 1 Real.log x :=
      Real.contDiffAt_log.mpr (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < T / 16) hx.1))
    exact ((contDiff_zetaGaussianQuadraticIntegral T hG.ne').of_le (by simp)).contDiffAt.comp x
      (hl.sub contDiffAt_const)
  have hdi : IntervalIntegrable
      (deriv (fun y => zetaGaussianQuadraticIntegral T G (Real.log y - Real.log A)))
      volume (T / 16) T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hinterval]
    intro x hx
    exact ((hs x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨by positivity, hs, ?_, ?_⟩
  · intro x hx
    exact (norm_zetaGaussianQuadraticIntegral_le_mass hT hG hGT _).trans (by
      have hp : 0 ≤ Real.sqrt Real.pi * G := by positivity
      nlinarith)
  · calc
      _ ≤ ∫ x in (T / 16)..T, (2 * Real.sqrt Real.pi * G) *
          ‖deriv (fun y : ℝ => (zetaLogGaussianEnvelope A G y : ℂ)) x‖ := by
        apply intervalIntegral.integral_mono_on hinterval hdi.norm
          ((henv.derivative_integrable hinterval).norm.const_mul (2 * Real.sqrt Real.pi * G))
        intro x hx
        exact norm_deriv_zetaQuadraticLogGaussian_le hT hG hGT
          (lt_of_lt_of_le (by positivity : 0 < T / 16) hx.1) A
      _ = (2 * Real.sqrt Real.pi * G) *
          (∫ x in (T / 16)..T, ‖deriv (fun y : ℝ => (zetaLogGaussianEnvelope A G y : ℂ)) x‖) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (2 * Real.sqrt Real.pi * G) * 2 :=
        mul_le_mul_of_nonneg_left henv.variation_le (by positivity)
      _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
