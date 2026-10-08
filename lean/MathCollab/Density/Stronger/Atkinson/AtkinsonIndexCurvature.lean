module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexPhase

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonRealCurvature` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# Curvature of the real-index Atkinson phase

This file proves the exact second derivative in the summation variable and
the corresponding identity for a difference of two source phases.  These
are the differential identities immediately preceding the exponent-pair
estimate in Heath--Brown's argument.
-/

namespace MathCollab.Density.Stronger.Atkinson

set_option autoImplicit false
noncomputable section

/-- The exact real-index slope of the Atkinson phase. -/
def atkinsonIndexRealSlope (T x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ))

/-- The exact real-index curvature of the Atkinson phase. -/
def atkinsonIndexRealCurvature (T x : ℝ) : ℝ :=
  -(Real.pi * T) /
    (x ^ (2 : ℕ) * atkinsonIndexRealSlope T x)

theorem atkinsonIndexRealSlope_pos
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    0 < atkinsonIndexRealSlope T x := by
  unfold atkinsonIndexRealSlope
  apply Real.sqrt_pos.2
  positivity

/-- Exact derivative of the phase slope, hence the second derivative of
the equation-(11) phase. -/
theorem hasDerivAt_atkinsonIndexRealSlope
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (atkinsonIndexRealSlope T)
      (atkinsonIndexRealCurvature T x) x := by
  have hdiv : HasDerivAt (fun u : ℝ => 2 * Real.pi * T / u)
      (-(2 * Real.pi * T) / x ^ (2 : ℕ)) x := by
    simpa using! (hasDerivAt_const x (2 * Real.pi * T)).div
      (hasDerivAt_id x) hx.ne'
  have hradicand : HasDerivAt
      (fun u : ℝ => 2 * Real.pi * T / u + Real.pi ^ (2 : ℕ))
      (-(2 * Real.pi * T) / x ^ (2 : ℕ)) x := by
    simpa only [add_zero] using! hdiv.add
      (hasDerivAt_const x (Real.pi ^ (2 : ℕ)))
  have hpos : 0 < 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    positivity
  have hsqrt := hradicand.sqrt hpos.ne'
  unfold atkinsonIndexRealSlope atkinsonIndexRealCurvature
  convert hsqrt using 1
  simp only [atkinsonIndexRealSlope]
  ring

/-- The literal source phase has the exact second derivative displayed by
`atkinsonIndexRealCurvature`. -/
theorem hasDerivAt_deriv_atkinsonIndexRealPhase
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (fun u => deriv (atkinsonIndexRealPhase T) u)
      (atkinsonIndexRealCurvature T x) x := by
  have hev : (fun u => deriv (atkinsonIndexRealPhase T) u) =ᶠ[nhds x]
      atkinsonIndexRealSlope T := by
    filter_upwards [eventually_gt_nhds hx] with u hu
    rw [(hasDerivAt_atkinsonIndexRealPhase hT hu).deriv]
    rfl
  exact (hasDerivAt_atkinsonIndexRealSlope hT hx).congr_of_eventuallyEq
    hev

/-- Difference of two exact Atkinson phases, with the later height first. -/
def atkinsonIndexPhaseDifference (t u x : ℝ) : ℝ :=
  atkinsonIndexRealPhase t x - atkinsonIndexRealPhase u x

/-- Exact first derivative of the phase difference. -/
theorem hasDerivAt_atkinsonIndexPhaseDifference
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (atkinsonIndexPhaseDifference t u)
      (atkinsonIndexRealSlope t x -
        atkinsonIndexRealSlope u x) x := by
  unfold atkinsonIndexPhaseDifference atkinsonIndexRealSlope
  exact (hasDerivAt_atkinsonIndexRealPhase ht hx).sub
    (hasDerivAt_atkinsonIndexRealPhase hu hx)

/-- Exact second derivative of the phase difference. -/
theorem hasDerivAt_atkinsonIndexPhaseDifferenceSlope
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt
      (fun y => atkinsonIndexRealSlope t y -
        atkinsonIndexRealSlope u y)
      (atkinsonIndexRealCurvature t x -
        atkinsonIndexRealCurvature u x) x :=
  (hasDerivAt_atkinsonIndexRealSlope ht hx).sub
    (hasDerivAt_atkinsonIndexRealSlope hu hx)

theorem atkinsonIndexRealCurvature_neg
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    atkinsonIndexRealCurvature T x < 0 := by
  unfold atkinsonIndexRealCurvature
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos Real.pi_pos hT))
    (mul_pos (sq_pos_of_pos hx) (atkinsonIndexRealSlope_pos hT hx))


end

end MathCollab.Density.Stronger.Atkinson
