module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiTest
public import Mathlib.Analysis.MellinInversion

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

noncomputable def dfiVoronoiInvWeight (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * g x

/-- The `invWeight` definition used by the source-facing construction in `DFIProposition1`. -/
noncomputable def DFIVoronoiTestFunction.invWeight
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    DFIVoronoiTestFunction (dfiVoronoiInvWeight g) := by
  refine ⟨hg.lower, hg.upper, hg.lower_pos, hg.lower_le_upper, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      have hEventually : dfiVoronoiInvWeight g =ᶠ[nhds (0 : ℝ)] 0 := by
        filter_upwards [Iio_mem_nhds hg.lower_pos] with y hy
        have hgy : g y = 0 := by
          by_contra hne
          exact (not_le_of_gt hy) (hg.support_subset hne).1
        simp [dfiVoronoiInvWeight, hgy]
      exact contDiffAt_const.congr_of_eventuallyEq hEventually
    · have hCast : ContDiffAt ℝ ∞ (fun y : ℝ ↦ (y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt
      have hCastNe : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      exact (hCast.inv hCastNe).mul hg.smooth.contDiffAt
  · intro x hx
    apply hg.support_subset
    intro hgx
    exact hx (by simp [dfiVoronoiInvWeight, hgx])

/-- The inverse source weight translates the Mellin transform exactly one
unit to the right. -/
theorem DFIVoronoiTestFunction.mellin_invWeight_add_one
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (z : ℂ) :
    mellin (dfiVoronoiInvWeight g) (z + 1) = mellin g z := by
  unfold mellin
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show z + 1 - 1 = z by ring]
    rw [show z - 1 = z + (-1 : ℂ) by ring]
    rw [Complex.cpow_add _ _ hxC, Complex.cpow_neg_one]
    simp only [dfiVoronoiInvWeight]
    ring
  · have hgx : g x = 0 := by
      by_contra hne
      have hs := hg.support_subset hne
      exact hx (hg.lower_pos.trans_le hs.1)
    simp [dfiVoronoiInvWeight, hgx]

/-- Repeated multiplication by the inverse source variable.  This is the
Mellin-coordinate implementation of the repeated integration by parts used
to truncate the Bessel transforms in DFI equation (29). -/
noncomputable def dfiVoronoiInvWeightIterate :
    ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | k + 1, g => dfiVoronoiInvWeight (dfiVoronoiInvWeightIterate k g)

@[simp]
theorem dfiVoronoiInvWeightIterate_zero (g : ℝ → ℂ) :
    dfiVoronoiInvWeightIterate 0 g = g := rfl

@[simp]
theorem dfiVoronoiInvWeightIterate_succ (k : ℕ) (g : ℝ → ℂ) :
    dfiVoronoiInvWeightIterate (k + 1) g =
      dfiVoronoiInvWeight (dfiVoronoiInvWeightIterate k g) := rfl

/-- Every repeated inverse weight remains a smooth positive compactly
supported Voronoi test function with the original support endpoints. -/
noncomputable def DFIVoronoiTestFunction.invWeightIterate
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) :
    DFIVoronoiTestFunction (dfiVoronoiInvWeightIterate k g) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      simpa [dfiVoronoiInvWeightIterate] using ih.invWeight

/-- `k` repeated inverse weights translate the Mellin transform exactly
`k` units to the right. -/
theorem DFIVoronoiTestFunction.mellin_invWeightIterate_add_nat
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) (z : ℂ) :
    mellin (dfiVoronoiInvWeightIterate k g) (z + k) = mellin g z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := (hg.invWeightIterate k).mellin_invWeight_add_one (z + k)
      rw [show z + (k + 1 : ℕ) = (z + k) + 1 by push_cast; ring]
      rw [dfiVoronoiInvWeightIterate_succ, hstep, ih]


end MathCollab.Density.Stronger.Atkinson
