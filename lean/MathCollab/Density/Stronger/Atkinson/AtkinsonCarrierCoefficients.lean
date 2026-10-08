module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCoefficientVariation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonBesselScale (α : ℝ) (n : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-2 * α) * (n : ℝ) ^ (-α)

def neumannLeadingPlus : ℂ := -(1 + I) / 2
def neumannLeadingMinus : ℂ := -(1 - I) / 2
def neumannCorrectionPlus : ℂ := (1 - I) / 2
def neumannCorrectionMinus : ℂ := (1 + I) / 2

theorem atkinsonBesselScale_quarter_normalization (n : ℕ) :
    2*Real.sqrt Real.pi*atkinsonBesselScale (1/4) n = (n:ℝ)^(-(1/4:ℝ)) := by
  have hp : Real.sqrt (4*Real.pi) = 2*Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  unfold atkinsonBesselScale
  norm_num only [show (-2:ℝ)*(1/4) = -(1/2) by norm_num]
  rw [Real.rpow_neg (by positivity),← Real.sqrt_eq_rpow,hp]
  field_simp

end MathCollab.Density.Stronger.Atkinson
