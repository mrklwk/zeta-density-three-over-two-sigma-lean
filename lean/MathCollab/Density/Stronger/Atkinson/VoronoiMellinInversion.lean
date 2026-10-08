module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMellinKernel

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology
open Classical
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem DFIVoronoiTestFunction.eventuallyEq_zero_atTop
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    g =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop hg.upper] with x hx
  by_contra hne
  have hs := hg.support_subset hne
  exact (not_lt_of_ge hs.2) hx

theorem DFIVoronoiTestFunction.eventuallyEq_zero_atZero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0)) g 0 := by
  have hnear : ∀ᶠ x : ℝ in nhds (0 : ℝ), x < hg.lower :=
    isOpen_Iio.mem_nhds hg.lower_pos
  have hnear' : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x < hg.lower :=
    hnear.filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear'] with x hx
  by_contra hne
  have hs := hg.support_subset hne
  exact (not_lt_of_ge hs.1) hx

theorem DFIVoronoiTestFunction.isBigO_atTop
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (a : ℝ) :
    g =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  exact (Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-a)) atTop).congr'
    hg.eventuallyEq_zero_atTop.symm EventuallyEq.rfl

theorem DFIVoronoiTestFunction.isBigO_atZero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (b : ℝ) :
    Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0)) g
      (fun x : ℝ => x ^ (-b)) := by
  exact (Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-b))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))).congr'
    hg.eventuallyEq_zero_atZero.symm EventuallyEq.rfl

theorem DFIVoronoiTestFunction.mellinConvergent
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    MellinConvergent g (σ : ℂ) := by
  exact mellinConvergent_of_isBigO_rpow
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (σ + 1)) (by simp)
    (hg.isBigO_atZero (σ - 1)) (by simp)

/-- Pointwise Mellin inversion for the exact DFI source test class, with
all convergence and vertical-integrability hypotheses discharged. -/
theorem DFIVoronoiTestFunction.mellinInversion
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin g) x = g x := by
  exact mellinInv_mellin_eq σ g hx (hg.mellinConvergent σ)
    (hg.verticalIntegrable_mellin σ) hg.continuous.continuousAt


/-- For the source test class, Mellin differentiation at one has no
remaining convergence premise. -/
theorem DFIVoronoiTestFunction.mellin_hasDerivAt_one
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    HasDerivAt (mellin g) (mellin (fun x : ℝ => Real.log x • g x) 1) 1 := by
  exact (mellin_hasDerivAt_of_isBigO_rpow (s := (1 : ℂ)) (a := (2 : ℝ))
    (b := (0 : ℝ))
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (2 : ℝ)) (by norm_num)
    (hg.isBigO_atZero (0 : ℝ)) (by norm_num)).2

theorem mellin_apply_one (g : ℝ → ℂ) :
    mellin g 1 = ∫ x : ℝ in Set.Ioi 0, g x := by
  simp [mellin]

theorem mellin_log_smul_apply_one (g : ℝ → ℂ) :
    mellin (fun x : ℝ => Real.log x • g x) 1 =
      ∫ x : ℝ in Set.Ioi 0, (Real.log x : ℂ) * g x := by
  simp [mellin, smul_eq_mul]


end MathCollab.Density.Stronger.Atkinson
