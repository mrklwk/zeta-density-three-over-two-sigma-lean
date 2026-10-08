module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorLatticePhase
public import MathCollab.Density.Stronger.Atkinson.BesselK0
public import MathCollab.Density.Stronger.Atkinson.BesselY0

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonVoronoiMain (T G L : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) *
    zetaAtkinsonDivisorTest T G L x

def zetaAtkinsonBesselMinus (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * (-(2 * Real.pi) : ℂ) *
    ∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
      (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

def zetaAtkinsonBesselPlusTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * 4 * ∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
    (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

def zetaAtkinsonBesselPlus (T G L : ℝ) : ℂ := ∑' n : ℕ, zetaAtkinsonBesselPlusTerm T G L n

end MathCollab.Density.Stronger.Atkinson
