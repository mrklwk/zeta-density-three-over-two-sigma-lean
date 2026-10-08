module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_SIGNED_NORMALIZATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSignedSaddleProfile
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryMain

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem exp_positive_saddle_mul_fresnel (f : ℝ) :
    Complex.exp (((f + Real.pi / 4 : ℝ) : ℂ) * I) *
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) = Complex.exp ((f : ℂ) * I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_negative_saddle_mul_fresnel (f : ℝ) :
    Complex.exp (((-f - Real.pi / 4 : ℝ) : ℂ) * I) *
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) = (-I) * Complex.exp ((-f : ℂ) * I) := by
  have hquarter : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * I) = -I := by
    simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      Complex.exp_neg_pi_div_two_mul_I
  rw [← hquarter, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem atkinsonStationaryMain_sqrt {T : ℝ} (hT : 0 < T)
    (G L α : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L α (Real.sqrt n) =
      (2 * atkinsonSaddleProfile T G L α (Real.sqrt n) * atkinsonSaddleGaussian T G n *
        Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
          Complex.exp ((atkinsonSourcePhase T n : ℂ) * I)) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (Real.sqrt n)) : ℂ) := by
  rw [atkinsonStationaryMain_eq_phase hT, atkinsonRootKernel_at_saddle hT,
    exp_zetaAtkinsonPhase_saddle_sqrt hT n]
  change 2 * atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (Real.sqrt n)) * _ * _ = _
  rw [atkinsonPowerWeight_at_saddle hT G L α n]
  calc
    _ = (2 * atkinsonSaddleProfile T G L α (Real.sqrt n) * atkinsonSaddleGaussian T G n *
      Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
        (Complex.exp (((atkinsonSourcePhase T n + Real.pi / 4 : ℝ) : ℂ) * I) *
          Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I))) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (Real.sqrt n)) : ℂ) := by ring
    _ = _ := by rw [exp_positive_saddle_mul_fresnel]

theorem atkinsonStationaryMain_neg_sqrt {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L α (-Real.sqrt n) =
      ((-I) * 2 * atkinsonSaddleProfile T G L α (-Real.sqrt n) * atkinsonSaddleGaussian T G n *
        Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
          Complex.exp ((-atkinsonSourcePhase T n : ℂ) * I)) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (-Real.sqrt n)) : ℂ) := by
  rw [atkinsonStationaryMain_eq_phase hT, atkinsonRootKernel_at_saddle hT,
    exp_zetaAtkinsonPhase_saddle_neg_sqrt hT n]
  change 2 * atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (-Real.sqrt n)) * _ * _ = _
  rw [atkinsonPowerWeight_at_neg_saddle hT hG L α n]
  calc
    _ = (2 * atkinsonSaddleProfile T G L α (-Real.sqrt n) * atkinsonSaddleGaussian T G n *
      Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
        (Complex.exp (((-atkinsonSourcePhase T n - Real.pi / 4 : ℝ) : ℂ) * I) *
          Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I))) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (-Real.sqrt n)) : ℂ) := by ring
    _ = _ := by rw [exp_negative_saddle_mul_fresnel]; ring

end MathCollab.Density.Stronger.Atkinson
