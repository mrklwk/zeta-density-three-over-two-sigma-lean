module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.MainElementaryWeights
public import MathCollab.Density.Stronger.Atkinson.AtkinsonAmplitude
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCompactProfiles
public import MathCollab.Density.Stronger.Atkinson.ZetaQuadraticLogGaussianVariation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonMainWeight (T G L x : ℝ) : ℂ :=
  ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ) *
    (zetaDivisorBandCutoff T G L x : ℂ) * (Real.sqrt x : ℂ) *
      zetaMainMellinProfile (x / T) * zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem zetaAtkinsonMainWeight_eq_amplitude {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (G L : ℝ) :
    zetaAtkinsonMainWeight T G L x =
      (x : ℂ) * ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) *
        zetaAtkinsonAmplitude T G L x := by
  unfold zetaAtkinsonMainWeight zetaAtkinsonAmplitude
  rw [← zetaDivisorWeight_source_eq_profile hT hx, ← mul_exp_neg_half_log_eq_sqrt hx]
  push_cast
  ring

theorem zetaAtkinsonMainWeight_carrier {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (G L : ℝ) :
    zetaAtkinsonMainWeight T G L x * ((x : ℂ)⁻¹ *
      Complex.exp (((T * Real.log x - 2 * Real.pi * x : ℝ) : ℂ) * I)) =
        ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * zetaAtkinsonDivisorTest T G L x := by
  rw [zetaAtkinsonMainWeight_eq_amplitude hT hx G L,
    zetaAtkinsonDivisorTest_eq_amplitude_phase T G L hx]
  simp only [zetaAtkinsonPhase, mul_zero, zero_mul, add_zero]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp

theorem exists_intervalC1Bound_zetaAtkinsonMainWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
      0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (zetaAtkinsonMainWeight T G L) (T / 16) T
        (C * G * Real.sqrt T * Real.log T) := by
  obtain ⟨C, hC, hprofile⟩ := exists_intervalC1Bound_zetaMainMellinProfile
  refine ⟨768 * C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hlog hG hGT hL
  have hT0 : 0 < T := by linarith
  have hinterval : T / 16 ≤ T := by linarith
  have hphase : IntervalC1Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (T / 16) T 1 := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC1Bound_const (zetaSquareReflectedGammaPhase T) (T / 16) T
  have h := (((((intervalC1Bound_source_log hT).mul
    (intervalC1Bound_zetaDivisorBandCutoff hT0 hG hL hinterval) hinterval).mul
      (intervalC1Bound_source_sqrt hT0) hinterval).mul (hprofile T hT0) hinterval).mul
        hphase hinterval).mul (intervalC1Bound_zetaQuadraticLogGaussian hT0 hG hGT) hinterval
  apply h.mono
  have hp : 0 ≤ 256 * C * Real.sqrt Real.pi * G * Real.sqrt T := by positivity
  have hl := mul_le_mul_of_nonneg_left (sourceLogWeight_le_three_log hlog) hp
  convert hl using 1 <;> ring

end MathCollab.Density.Stronger.Atkinson
