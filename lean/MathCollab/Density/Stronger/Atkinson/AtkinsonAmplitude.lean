module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorLatticePhase
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonPhase

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonAmplitude (T G L x : ℝ) : ℂ :=
  (zetaDivisorBandCutoff T G L x : ℂ) * (Real.exp (-Real.log x / 2) : ℂ) *
    zetaDivisorWeight ((Real.log x : ℂ) - zetaGammaLeadingLog T) *
      zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem ofReal_cpow_critical_conjugate (T : ℝ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((-1 / 2 : ℂ) + (T : ℂ) * I) =
      (Real.exp (-Real.log x / 2) : ℂ) * Complex.exp ((T * Real.log x : ℝ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zetaAtkinsonDivisorTest_mul_carrier (T G L b : ℝ) {x : ℝ} (hx : 0 < x) :
    zetaAtkinsonDivisorTest T G L x *
      Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I) =
        zetaAtkinsonAmplitude T G L x * Complex.exp ((zetaAtkinsonPhase T b x : ℝ) * I) := by
  have hp : Complex.exp ((zetaAtkinsonPhase T b x : ℝ) * I) =
      Complex.exp ((-2 * Real.pi * x : ℝ) * I) *
        Complex.exp ((T * Real.log x : ℝ) * I) *
          Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold zetaAtkinsonPhase
    push_cast
    ring
  rw [hp]
  unfold zetaAtkinsonDivisorTest zetaDivisorLatticePhase zetaSmoothDivisorTest
    zetaShortDivisorTestFunction zetaAtkinsonAmplitude
  rw [ofReal_cpow_critical_conjugate T hx]
  ring

theorem zetaAtkinsonDivisorTest_eq_amplitude_phase (T G L : ℝ) {x : ℝ} (hx : 0 < x) :
    zetaAtkinsonDivisorTest T G L x =
      zetaAtkinsonAmplitude T G L x * Complex.exp ((zetaAtkinsonPhase T 0 x : ℝ) * I) := by
  simpa only [mul_zero, zero_mul, ofReal_zero, Complex.exp_zero, mul_one] using
    zetaAtkinsonDivisorTest_mul_carrier T G L 0 hx


end MathCollab.Density.Stronger.Atkinson
