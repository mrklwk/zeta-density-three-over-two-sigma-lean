module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

structure DFIVoronoiTestFunction (g : ℝ → ℂ) where
  /-- The `lower` component of `DFIVoronoiTestFunction`. -/
  lower : ℝ
  /-- The `upper` component of `DFIVoronoiTestFunction`. -/
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  smooth : ContDiff ℝ ∞ g
  support_subset : Function.support g ⊆ Set.Icc lower upper

theorem DFIVoronoiTestFunction.continuous
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) : Continuous g :=
  hg.smooth.continuous

theorem DFIVoronoiTestFunction.hasCompactSupport
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) : HasCompactSupport g := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hg.support_subset

end MathCollab.Density.Stronger.Atkinson
