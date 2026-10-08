module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_FINITE_ERROR_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerIntegral
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCarrierCoefficients
public import MathCollab.Density.Stronger.Fourth.Coefficients

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex Filter
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonLeadingIntegral (T G L : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt Real.pi / Real.pi : ℂ) * (atkinsonBesselScale (1 / 4) n : ℂ) *
    (neumannLeadingPlus * atkinsonPowerIntegral T G L (1 / 4) (Real.sqrt n) +
     neumannLeadingMinus * atkinsonPowerIntegral T G L (1 / 4) (-Real.sqrt n))

def atkinsonLeadingTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * atkinsonLeadingIntegral T G L n

def atkinsonLeadingSum (T G L : ℝ) : ℂ := ∑' n : ℕ, atkinsonLeadingTerm T G L n

def atkinsonLeadingFiniteSum (T G L : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonLeadingTerm T G L n

theorem atkinsonBesselScale_nonneg (α : ℝ) (n : ℕ) : 0 ≤ atkinsonBesselScale α n := by
  unfold atkinsonBesselScale
  positivity

end MathCollab.Density.Stronger.Atkinson
