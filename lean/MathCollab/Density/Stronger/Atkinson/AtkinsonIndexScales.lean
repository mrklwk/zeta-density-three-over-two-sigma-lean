module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexHeight

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonCurvatureScale` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# Uniform dyadic curvature scales for the Atkinson phase

On the source range `0 < x <= u <= c <= 2u`, the height derivative of the
curvature has size `u^(-1/2) x^(-3/2)`.  This file first records exact
radical bounds; the constants remain literal so no asymptotic convention is
hidden.
-/

namespace MathCollab.Density.Stronger.Atkinson

set_option autoImplicit false
noncomputable section

/-- Literal lower slope used in the dyadic curvature estimate. -/
def atkinsonIndexSlopeLower (u x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * u / x)

/-- Literal upper slope used in the dyadic curvature estimate. -/
def atkinsonIndexSlopeUpper (u x : ℝ) : ℝ :=
  Real.sqrt ((2 * Real.pi + Real.pi ^ (2 : ℕ)) * (2 * u) / x)

/-- Lower curvature-variation scale on a dyadic height box. -/
def atkinsonIndexCurvatureDerivativeLower (u x : ℝ) : ℝ :=
  Real.pi /
    (2 * x ^ (2 : ℕ) * atkinsonIndexSlopeUpper u x)

/-- Upper curvature-variation scale on a dyadic height box. -/
def atkinsonIndexCurvatureDerivativeUpper (u x : ℝ) : ℝ :=
  Real.pi /
    (x ^ (2 : ℕ) * atkinsonIndexSlopeLower u x)

/-- A uniform lower curvature scale for indices in `[A,B]`. -/
def atkinsonIndexBoxCurvatureLower (u A B : ℝ) : ℝ :=
  Real.pi / (2 * B ^ (2 : ℕ) * atkinsonIndexSlopeUpper u A)

/-- A uniform upper curvature scale for indices in `[A,B]`. -/
def atkinsonIndexBoxCurvatureUpper (u A B : ℝ) : ℝ :=
  Real.pi / (A ^ (2 : ℕ) * atkinsonIndexSlopeLower u B)

theorem atkinsonIndexSlopeLower_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < atkinsonIndexSlopeLower u x := by
  unfold atkinsonIndexSlopeLower
  exact Real.sqrt_pos.2 (div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hu) hx)

theorem atkinsonIndexSlopeUpper_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < atkinsonIndexSlopeUpper u x := by
  unfold atkinsonIndexSlopeUpper
  apply Real.sqrt_pos.2
  exact div_pos
    (mul_pos (add_pos (mul_pos (by norm_num) Real.pi_pos)
      (sq_pos_of_pos Real.pi_pos)) (mul_pos (by norm_num) hu)) hx

/-- Lower radical comparison on the source dyadic box. -/
theorem atkinsonIndexSlopeLower_le
    {u c x : ℝ} (hx : 0 < x) (huc : u ≤ c) :
    atkinsonIndexSlopeLower u x ≤
      atkinsonIndexRealSlope c x := by
  unfold atkinsonIndexSlopeLower atkinsonIndexRealSlope
  apply Real.sqrt_le_sqrt
  have hmul := mul_le_mul_of_nonneg_left huc
    (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) Real.pi_nonneg)
  have hdiv : 2 * Real.pi * u / x ≤ 2 * Real.pi * c / x :=
    div_le_div_of_nonneg_right hmul hx.le
  exact hdiv.trans (le_add_of_nonneg_right (sq_nonneg Real.pi))

/-- Upper radical comparison on the source dyadic box. -/
theorem atkinsonIndexSlope_le_upper
    {u c x : ℝ} (hu : 0 < u) (hx : 0 < x) (hxu : x ≤ u)
    (hcu : c ≤ 2 * u) :
    atkinsonIndexRealSlope c x ≤
      atkinsonIndexSlopeUpper u x := by
  unfold atkinsonIndexSlopeUpper atkinsonIndexRealSlope
  apply Real.sqrt_le_sqrt
  have hc2 : 2 * c ≤ 2 * (2 * u) := by linarith
  have hxu' : Real.pi * x ≤ Real.pi * (2 * u) := by
    have : x ≤ 2 * u := hxu.trans (by linarith)
    exact mul_le_mul_of_nonneg_left this Real.pi_nonneg
  rw [le_div_iff₀ hx]
  field_simp [hx.ne']
  nlinarith

theorem atkinsonIndexCurvatureDerivativeLower_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < atkinsonIndexCurvatureDerivativeLower u x := by
  unfold atkinsonIndexCurvatureDerivativeLower
  exact div_pos Real.pi_pos
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx))
      (atkinsonIndexSlopeUpper_pos hu hx))

theorem atkinsonIndexCurvatureDerivativeUpper_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < atkinsonIndexCurvatureDerivativeUpper u x := by
  unfold atkinsonIndexCurvatureDerivativeUpper
  exact div_pos Real.pi_pos
    (mul_pos (sq_pos_of_pos hx)
      (atkinsonIndexSlopeLower_pos hu hx))

theorem atkinsonIndexSlopeUpper_anti
    {u A x : ℝ} (hu : 0 < u) (hA : 0 < A) (hAx : A ≤ x) :
    atkinsonIndexSlopeUpper u x ≤
      atkinsonIndexSlopeUpper u A := by
  unfold atkinsonIndexSlopeUpper
  apply Real.sqrt_le_sqrt
  have hnum : 0 ≤ (2 * Real.pi + Real.pi ^ (2 : ℕ)) * (2 * u) := by
    positivity
  exact div_le_div_of_nonneg_left hnum hA hAx

theorem atkinsonIndexSlopeLower_anti
    {u x B : ℝ} (hu : 0 < u) (hx : 0 < x) (hxB : x ≤ B) :
    atkinsonIndexSlopeLower u B ≤
      atkinsonIndexSlopeLower u x := by
  unfold atkinsonIndexSlopeLower
  apply Real.sqrt_le_sqrt
  have hnum : 0 ≤ 2 * Real.pi * u := by positivity
  exact div_le_div_of_nonneg_left hnum hx hxB

/-- Uniformize the pointwise curvature bounds on a closed index box. -/
theorem atkinsonIndexCurvatureDerivative_box_bounds
    {u A x B : ℝ} (hu : 0 < u) (hA : 0 < A) (hAx : A ≤ x)
    (hxB : x ≤ B) :
    atkinsonIndexBoxCurvatureLower u A B ≤
        atkinsonIndexCurvatureDerivativeLower u x ∧
      atkinsonIndexCurvatureDerivativeUpper u x ≤
        atkinsonIndexBoxCurvatureUpper u A B := by
  have hx : 0 < x := hA.trans_le hAx
  have hB : 0 < B := hx.trans_le hxB
  have hupperAnti := atkinsonIndexSlopeUpper_anti hu hA hAx
  have hlowerAnti := atkinsonIndexSlopeLower_anti hu hx hxB
  have hxSq : x ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hx.le hxB 2
  have hASq : A ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hA.le hAx 2
  constructor
  · unfold atkinsonIndexBoxCurvatureLower
      atkinsonIndexCurvatureDerivativeLower
    have hden :
        2 * x ^ (2 : ℕ) * atkinsonIndexSlopeUpper u x ≤
          2 * B ^ (2 : ℕ) * atkinsonIndexSlopeUpper u A := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hxSq (by norm_num)) hupperAnti
        (atkinsonIndexSlopeUpper_pos hu hx).le
        (mul_nonneg (by norm_num) (sq_nonneg B))
    exact div_le_div_of_nonneg_left Real.pi_nonneg
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx))
        (atkinsonIndexSlopeUpper_pos hu hx)) hden
  · unfold atkinsonIndexBoxCurvatureUpper
      atkinsonIndexCurvatureDerivativeUpper
    have hden :
        A ^ (2 : ℕ) * atkinsonIndexSlopeLower u B ≤
          x ^ (2 : ℕ) * atkinsonIndexSlopeLower u x := by
      exact mul_le_mul hASq hlowerAnti
        (atkinsonIndexSlopeLower_pos hu hB).le (sq_nonneg x)
    exact div_le_div_of_nonneg_left Real.pi_nonneg
      (mul_pos (sq_pos_of_pos hA)
        (atkinsonIndexSlopeLower_pos hu hB)) hden

/-- Exact derivative squeezed between its literal dyadic lower and upper
scales. -/
theorem atkinsonIndexCurvatureDerivative_bounds
    {u c x : ℝ} (hu : 0 < u) (hx : 0 < x) (hxu : x ≤ u)
    (huc : u ≤ c) (hcu : c ≤ 2 * u) :
    atkinsonIndexCurvatureDerivativeLower u x ≤
        Real.pi / x ^ (2 : ℕ) *
          (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
          (atkinsonIndexRealSlope c x) ^ (3 : ℕ) ∧
      Real.pi / x ^ (2 : ℕ) *
          (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
          (atkinsonIndexRealSlope c x) ^ (3 : ℕ) ≤
        atkinsonIndexCurvatureDerivativeUpper u x := by
  have hc : 0 < c := hu.trans_le huc
  have hspos := atkinsonIndexRealSlope_pos hc hx
  have hslow := atkinsonIndexSlopeLower_le hx huc
  have hsup := atkinsonIndexSlope_le_upper hu hx hxu hcu
  have hsquare :
      (atkinsonIndexRealSlope c x) ^ 2 =
        2 * Real.pi * c / x + Real.pi ^ (2 : ℕ) := by
    unfold atkinsonIndexRealSlope
    rw [Real.sq_sqrt]
    positivity
  have hhalf :
      (atkinsonIndexRealSlope c x) ^ 2 / 2 ≤
        Real.pi * c / x + Real.pi ^ (2 : ℕ) := by
    calc
      (atkinsonIndexRealSlope c x) ^ 2 / 2 =
          Real.pi * c / x + Real.pi ^ (2 : ℕ) / 2 := by
        rw [hsquare]
        ring
      _ ≤ Real.pi * c / x + Real.pi ^ (2 : ℕ) := by
        linarith [sq_nonneg Real.pi]
  have hwhole :
      Real.pi * c / x + Real.pi ^ (2 : ℕ) ≤
        (atkinsonIndexRealSlope c x) ^ 2 := by
    rw [hsquare]
    have hp := div_nonneg (mul_nonneg Real.pi_nonneg hc.le) hx.le
    calc
      Real.pi * c / x + Real.pi ^ (2 : ℕ) ≤
          Real.pi * c / x +
            (Real.pi * c / x + Real.pi ^ (2 : ℕ)) := by
        exact le_add_of_nonneg_left hp
      _ = 2 * Real.pi * c / x + Real.pi ^ (2 : ℕ) := by ring
  constructor
  · have hden :
        2 * x ^ (2 : ℕ) * atkinsonIndexRealSlope c x ≤
          2 * x ^ (2 : ℕ) * atkinsonIndexSlopeUpper u x := by
      exact mul_le_mul_of_nonneg_left hsup
        (mul_nonneg (by norm_num) (sq_nonneg x))
    have hrecip :
        Real.pi /
            (2 * x ^ (2 : ℕ) * atkinsonIndexSlopeUpper u x) ≤
          Real.pi /
            (2 * x ^ (2 : ℕ) * atkinsonIndexRealSlope c x) := by
      exact div_le_div_of_nonneg_left Real.pi_nonneg
        (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx)) hspos) hden
    rw [atkinsonIndexCurvatureDerivativeLower]
    refine hrecip.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (div_nonneg Real.pi_nonneg (sq_nonneg x))
    have hpow : 0 < (atkinsonIndexRealSlope c x) ^ (3 : ℕ) := by
      positivity
    calc
      Real.pi / (2 * x ^ (2 : ℕ) * atkinsonIndexRealSlope c x) =
          (Real.pi / x ^ (2 : ℕ)) *
            ((atkinsonIndexRealSlope c x) ^ 2 / 2) /
            (atkinsonIndexRealSlope c x) ^ (3 : ℕ) := by
        field_simp [hx.ne', hspos.ne']
      _ ≤ (Real.pi / x ^ (2 : ℕ)) *
            (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
            (atkinsonIndexRealSlope c x) ^ (3 : ℕ) := by
        exact div_le_div_of_nonneg_right hmul hpow.le
  · have hmul := mul_le_mul_of_nonneg_left hwhole
      (div_nonneg Real.pi_nonneg (sq_nonneg x))
    have hpow : 0 < (atkinsonIndexRealSlope c x) ^ (3 : ℕ) := by
      positivity
    have hfirst :
        (Real.pi / x ^ (2 : ℕ)) *
            (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
            (atkinsonIndexRealSlope c x) ^ (3 : ℕ) ≤
          Real.pi /
            (x ^ (2 : ℕ) * atkinsonIndexRealSlope c x) := by
      calc
        (Real.pi / x ^ (2 : ℕ)) *
              (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
              (atkinsonIndexRealSlope c x) ^ (3 : ℕ) ≤
            (Real.pi / x ^ (2 : ℕ)) *
              (atkinsonIndexRealSlope c x) ^ 2 /
              (atkinsonIndexRealSlope c x) ^ (3 : ℕ) := by
          exact div_le_div_of_nonneg_right hmul hpow.le
        _ = Real.pi /
              (x ^ (2 : ℕ) * atkinsonIndexRealSlope c x) := by
          field_simp [hx.ne', hspos.ne']
    refine hfirst.trans ?_
    rw [atkinsonIndexCurvatureDerivativeUpper]
    have hden :
        x ^ (2 : ℕ) * atkinsonIndexSlopeLower u x ≤
          x ^ (2 : ℕ) * atkinsonIndexRealSlope c x :=
      mul_le_mul_of_nonneg_left hslow (sq_nonneg x)
    exact div_le_div_of_nonneg_left Real.pi_nonneg
      (mul_pos (sq_pos_of_pos hx) (atkinsonIndexSlopeLower_pos hu hx)) hden

/-- Quantitative phase-curvature comparison between two heights in one
dyadic box. -/
theorem atkinsonIndexCurvatureDifference_bounds
    {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x)
    (hxu : x ≤ u) (htuUpper : t ≤ 2 * u) :
    atkinsonIndexCurvatureDerivativeLower u x * (t - u) ≤
        -(atkinsonIndexRealCurvature t x -
          atkinsonIndexRealCurvature u x) ∧
      -(atkinsonIndexRealCurvature t x -
          atkinsonIndexRealCurvature u x) ≤
        atkinsonIndexCurvatureDerivativeUpper u x * (t - u) := by
  obtain ⟨c, hc, heq⟩ :=
    exists_atkinsonIndexCurvatureDifference_eq hu htu hx
  have hcBounds := atkinsonIndexCurvatureDerivative_bounds hu hx hxu
    hc.1.le (hc.2.le.trans htuUpper)
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_right hcBounds.1 (sub_nonneg.mpr htu.le),
    mul_le_mul_of_nonneg_right hcBounds.2 (sub_nonneg.mpr htu.le)⟩


end

end MathCollab.Density.Stronger.Atkinson
