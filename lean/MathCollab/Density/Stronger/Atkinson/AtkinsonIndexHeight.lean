module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexCurvature
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonCurvatureHeight` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# Height variation of Atkinson curvature

The phase-difference estimate compares the curvatures at two separated
heights.  Here the positive curvature magnitude is differentiated in the
height variable.  This is the exact source quantity; later scale bounds are
obtained from this formula.
-/

open Set

namespace MathCollab.Density.Stronger.Atkinson

set_option autoImplicit false
noncomputable section

/-- Positive magnitude of the (negative) real-index curvature. -/
def atkinsonIndexCurvatureMagnitude (T x : ℝ) : ℝ :=
  Real.pi * T /
    (x ^ (2 : ℕ) * atkinsonIndexRealSlope T x)

theorem atkinsonIndexCurvatureMagnitude_eq_neg
    (T x : ℝ) :
    atkinsonIndexCurvatureMagnitude T x =
      -atkinsonIndexRealCurvature T x := by
  unfold atkinsonIndexCurvatureMagnitude
    atkinsonIndexRealCurvature
  ring

theorem atkinsonIndexCurvatureMagnitude_pos
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    0 < atkinsonIndexCurvatureMagnitude T x := by
  unfold atkinsonIndexCurvatureMagnitude
  exact div_pos (mul_pos Real.pi_pos hT)
    (mul_pos (sq_pos_of_pos hx) (atkinsonIndexRealSlope_pos hT hx))

/-- Height derivative of the exact real-index slope. -/
theorem hasDerivAt_atkinsonIndexRealSlope_height
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (fun u => atkinsonIndexRealSlope u x)
      (Real.pi / (x * atkinsonIndexRealSlope T x)) T := by
  have hlin : HasDerivAt
      (fun u : ℝ => 2 * Real.pi * u / x + Real.pi ^ (2 : ℕ))
      (2 * Real.pi / x) T := by
    simpa only [mul_one, id_eq] using!
      (((hasDerivAt_id T).const_mul (2 * Real.pi)).div_const x).add_const
        (Real.pi ^ (2 : ℕ))
  have hpos : 0 < 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    positivity
  have hsqrt := hlin.sqrt hpos.ne'
  unfold atkinsonIndexRealSlope
  convert hsqrt using 1
  ring

/-- Exact height derivative of the positive curvature magnitude. -/
theorem hasDerivAt_atkinsonIndexCurvatureMagnitude
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (fun u => atkinsonIndexCurvatureMagnitude u x)
      (Real.pi / x ^ (2 : ℕ) *
        (Real.pi * T / x + Real.pi ^ (2 : ℕ)) /
        (atkinsonIndexRealSlope T x) ^ (3 : ℕ)) T := by
  have hs := hasDerivAt_atkinsonIndexRealSlope_height hT hx
  have hden : HasDerivAt
      (fun u => x ^ (2 : ℕ) * atkinsonIndexRealSlope u x)
      (x ^ (2 : ℕ) *
        (Real.pi / (x * atkinsonIndexRealSlope T x))) T :=
    hs.const_mul (x ^ (2 : ℕ))
  have hdenpos : 0 <
      x ^ (2 : ℕ) * atkinsonIndexRealSlope T x := by
    exact mul_pos (sq_pos_of_pos hx)
      (atkinsonIndexRealSlope_pos hT hx)
  have hnum : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi T := by
    simpa only [mul_one] using! (hasDerivAt_id T).const_mul Real.pi
  have hquot := hnum.div hden hdenpos.ne'
  unfold atkinsonIndexCurvatureMagnitude
  convert hquot using 1
  have hspos := atkinsonIndexRealSlope_pos hT hx
  have hsquare :
      (atkinsonIndexRealSlope T x) ^ 2 =
        2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    unfold atkinsonIndexRealSlope
    rw [Real.sq_sqrt]
    positivity
  have hsquare_mul :
      x * (atkinsonIndexRealSlope T x) ^ 2 =
        2 * Real.pi * T + Real.pi ^ (2 : ℕ) * x := by
    calc
      x * (atkinsonIndexRealSlope T x) ^ 2 =
          x * (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ)) := by
        rw [hsquare]
      _ = 2 * Real.pi * T + Real.pi ^ (2 : ℕ) * x := by
        field_simp [hx.ne']
  field_simp [hx.ne', hspos.ne']
  nlinarith [hsquare_mul]

theorem atkinsonIndexCurvatureMagnitude_deriv_pos
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    0 < Real.pi / x ^ (2 : ℕ) *
        (Real.pi * T / x + Real.pi ^ (2 : ℕ)) /
        (atkinsonIndexRealSlope T x) ^ (3 : ℕ) := by
  exact div_pos
    (mul_pos
      (div_pos Real.pi_pos (sq_pos_of_pos hx))
      (add_pos (div_pos (mul_pos Real.pi_pos hT) hx)
        (sq_pos_of_pos Real.pi_pos)))
    (pow_pos (atkinsonIndexRealSlope_pos hT hx) 3)

/-- The magnitude of the Atkinson curvature is strictly increasing with
height on the physical half-line. -/
theorem strictMonoOn_atkinsonIndexCurvatureMagnitude (x : ℝ)
    (hx : 0 < x) :
    StrictMonoOn (fun T => atkinsonIndexCurvatureMagnitude T x)
      (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro T hT
    exact (hasDerivAt_atkinsonIndexCurvatureMagnitude hT hx).continuousAt.continuousWithinAt
  · intro T hT
    simp only [interior_Ioi, mem_Ioi] at hT
    rw [(hasDerivAt_atkinsonIndexCurvatureMagnitude hT hx).deriv]
    exact atkinsonIndexCurvatureMagnitude_deriv_pos hT hx

/-- Curvature difference has the source sign when the first height is the
larger one. -/
theorem atkinsonIndexCurvatureDifference_neg
    {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    atkinsonIndexRealCurvature t x -
        atkinsonIndexRealCurvature u x < 0 := by
  have hmag := strictMonoOn_atkinsonIndexCurvatureMagnitude x hx hu
    (hu.trans htu) htu
  have het := atkinsonIndexCurvatureMagnitude_eq_neg t x
  have heu := atkinsonIndexCurvatureMagnitude_eq_neg u x
  linarith

/-- Mean-value representation of the curvature difference in the height
variable. -/
theorem exists_atkinsonIndexCurvatureDifference_eq
    {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    ∃ c ∈ Set.Ioo u t,
      -(atkinsonIndexRealCurvature t x -
          atkinsonIndexRealCurvature u x) =
        (Real.pi / x ^ (2 : ℕ) *
          (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
          (atkinsonIndexRealSlope c x) ^ (3 : ℕ)) * (t - u) := by
  let F : ℝ → ℝ := fun v => atkinsonIndexCurvatureMagnitude v x
  let F' : ℝ → ℝ := fun v =>
    Real.pi / x ^ (2 : ℕ) *
      (Real.pi * v / x + Real.pi ^ (2 : ℕ)) /
      (atkinsonIndexRealSlope v x) ^ (3 : ℕ)
  have hcont : ContinuousOn F (Set.Icc u t) := by
    intro v hv
    exact (hasDerivAt_atkinsonIndexCurvatureMagnitude
      (hu.trans_le hv.1) hx).continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ Set.Ioo u t, HasDerivAt F (F' v) v := by
    intro v hv
    exact hasDerivAt_atkinsonIndexCurvatureMagnitude
      (hu.trans hv.1) hx
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope F F' htu hcont hderiv
  refine ⟨c, hc, ?_⟩
  dsimp only [F, F'] at heq ⊢
  rw [atkinsonIndexCurvatureMagnitude_eq_neg,
    atkinsonIndexCurvatureMagnitude_eq_neg] at heq
  rw [heq]
  field_simp [sub_ne_zero.mpr htu.ne']
  ring


end

end MathCollab.Density.Stronger.Atkinson
