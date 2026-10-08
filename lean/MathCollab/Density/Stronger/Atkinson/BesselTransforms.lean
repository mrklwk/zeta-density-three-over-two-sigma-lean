module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIBesselKernel.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselY0Mellin
public import MathCollab.Density.Stronger.Atkinson.BesselMellinPairing

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

noncomputable def dfiVoronoiPlusBesselTransform
    (q : ℕ) [NeZero q] (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  (4 / (q : ℂ)) * ∫ x in Set.Ioi (0 : ℝ),
    g x * (dfiBesselK0
      (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)

/-- The literal equal-sign Bessel transform in DFI Proposition 1. -/
-- The parameter records the source-domain or uniformity contract even though the body is independent of it.
@[nolint unusedArguments]
noncomputable def dfiVoronoiMinusBesselTransform
    (q : ℕ) [NeZero q] (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  (-(2 * Real.pi) / (q : ℂ)) * ∫ x in Set.Ioi (0 : ℝ),
    g x * (dfiBesselY0
      (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)


end MathCollab.Density.Stronger.Atkinson
