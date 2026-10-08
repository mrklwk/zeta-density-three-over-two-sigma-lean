module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexBProcess
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonFirstDerivative` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# First-derivative bounds for differences of Atkinson phases

This file supplies the first-derivative alternative used together with the
`(1/2,1/2)` B-process in Ivić (7.19).  The bounds retain literal radical
scales on a dyadic index box; no exponent-pair estimate is postulated.
-/

open Set

namespace MathCollab.Density.Stronger.Atkinson

set_option autoImplicit false
noncomputable section

/-- Lower first-derivative scale for two heights separated by `t-u` and
indices in `[A,B]`. -/
def atkinsonIndexFirstDerivativeLower
    (u t A B : ℝ) : ℝ :=
  Real.pi * (t - u) /
    (B * atkinsonIndexSlopeUpper u A)

/-- Upper first-derivative scale on the same box. -/
def atkinsonIndexFirstDerivativeUpper
    (u t A B : ℝ) : ℝ :=
  Real.pi * (t - u) /
    (A * atkinsonIndexSlopeLower u B)

/-- Rationalization of the exact square-root slope difference. -/
theorem atkinsonIndexRealSlope_sub_eq
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    atkinsonIndexRealSlope t x -
        atkinsonIndexRealSlope u x =
      (2 * Real.pi * (t - u) / x) /
        (atkinsonIndexRealSlope t x +
          atkinsonIndexRealSlope u x) := by
  have hst := atkinsonIndexRealSlope_pos ht hx
  have hsu := atkinsonIndexRealSlope_pos hu hx
  have hden : atkinsonIndexRealSlope t x +
      atkinsonIndexRealSlope u x ≠ 0 := by positivity
  have htsq : (atkinsonIndexRealSlope t x) ^ (2 : ℕ) =
      2 * Real.pi * t / x + Real.pi ^ (2 : ℕ) := by
    unfold atkinsonIndexRealSlope
    rw [Real.sq_sqrt]
    positivity
  have husq : (atkinsonIndexRealSlope u x) ^ (2 : ℕ) =
      2 * Real.pi * u / x + Real.pi ^ (2 : ℕ) := by
    unfold atkinsonIndexRealSlope
    rw [Real.sq_sqrt]
    positivity
  apply (eq_div_iff hden).2
  calc
    (atkinsonIndexRealSlope t x -
          atkinsonIndexRealSlope u x) *
        (atkinsonIndexRealSlope t x +
          atkinsonIndexRealSlope u x) =
        (atkinsonIndexRealSlope t x) ^ (2 : ℕ) -
          (atkinsonIndexRealSlope u x) ^ (2 : ℕ) := by ring
    _ = 2 * Real.pi * (t - u) / x := by rw [htsq, husq]; ring

/-- Pointwise first-derivative bounds on a dyadic height/index box. -/
theorem atkinsonIndexRealSlopeDifference_box_bounds
    {t u A x B : ℝ}
    (hu : 0 < u) (htu : u < t) (hA : 0 < A)
    (hAx : A ≤ x) (hxB : x ≤ B) (hBu : B ≤ u)
    (htUpper : t ≤ 2 * u) :
    atkinsonIndexFirstDerivativeLower u t A B ≤
        atkinsonIndexRealSlope t x -
          atkinsonIndexRealSlope u x ∧
      atkinsonIndexRealSlope t x -
          atkinsonIndexRealSlope u x ≤
        atkinsonIndexFirstDerivativeUpper u t A B := by
  have hx : 0 < x := hA.trans_le hAx
  have hB : 0 < B := hx.trans_le hxB
  have ht : 0 < t := hu.trans htu
  have hgap : 0 < t - u := sub_pos.mpr htu
  have hstPos := atkinsonIndexRealSlope_pos ht hx
  have hsuPos := atkinsonIndexRealSlope_pos hu hx
  have hupperApos := atkinsonIndexSlopeUpper_pos hu hA
  have hlowerBpos := atkinsonIndexSlopeLower_pos hu hB
  have hupperX := atkinsonIndexSlopeUpper_anti hu hA hAx
  have hstUpper := atkinsonIndexSlope_le_upper
    (u := u) (c := t) hu hx (hxB.trans hBu) htUpper
  have huu : u ≤ 2 * u := by linarith
  have hsuUpper := atkinsonIndexSlope_le_upper
    (u := u) (c := u) hu hx (hxB.trans hBu) huu
  have hlowerX := atkinsonIndexSlopeLower_anti hu hx hxB
  have hstLower := atkinsonIndexSlopeLower_le
    (u := u) (c := t) hx htu.le
  have hsuLower := atkinsonIndexSlopeLower_le
    (u := u) (c := u) hx le_rfl
  have hdenUpper :
      x * (atkinsonIndexRealSlope t x +
        atkinsonIndexRealSlope u x) ≤
      B * (2 * atkinsonIndexSlopeUpper u A) := by
    have hsum : atkinsonIndexRealSlope t x +
        atkinsonIndexRealSlope u x ≤
        2 * atkinsonIndexSlopeUpper u A := by
      linarith [hstUpper.trans hupperX, hsuUpper.trans hupperX]
    exact mul_le_mul hxB hsum (add_nonneg hstPos.le hsuPos.le) hB.le
  have hdenLower :
      A * (2 * atkinsonIndexSlopeLower u B) ≤
      x * (atkinsonIndexRealSlope t x +
        atkinsonIndexRealSlope u x) := by
    have hsum : 2 * atkinsonIndexSlopeLower u B ≤
        atkinsonIndexRealSlope t x +
          atkinsonIndexRealSlope u x := by
      linarith [hlowerX.trans hstLower, hlowerX.trans hsuLower]
    exact mul_le_mul hAx hsum (mul_nonneg (by norm_num) hlowerBpos.le) hx.le
  have hnum : 0 ≤ 2 * Real.pi * (t - u) := by positivity
  have hdenUpperPos : 0 < B *
      (2 * atkinsonIndexSlopeUpper u A) :=
    mul_pos hB (mul_pos (by norm_num) hupperApos)
  have hdenLowerPos : 0 < A *
      (2 * atkinsonIndexSlopeLower u B) :=
    mul_pos hA (mul_pos (by norm_num) hlowerBpos)
  have hdenActualPos : 0 < x *
      (atkinsonIndexRealSlope t x +
        atkinsonIndexRealSlope u x) :=
    mul_pos hx (add_pos hstPos hsuPos)
  have hsumPos : 0 < atkinsonIndexRealSlope t x +
      atkinsonIndexRealSlope u x := add_pos hstPos hsuPos
  rw [atkinsonIndexRealSlope_sub_eq ht hu hx]
  constructor
  · unfold atkinsonIndexFirstDerivativeLower
    have hdiv := div_le_div_of_nonneg_left hnum hdenActualPos hdenUpper
    calc
      Real.pi * (t - u) /
          (B * atkinsonIndexSlopeUpper u A) =
          (2 * Real.pi * (t - u)) /
            (B * (2 * atkinsonIndexSlopeUpper u A)) := by ring
      _ ≤ (2 * Real.pi * (t - u)) /
          (x * (atkinsonIndexRealSlope t x +
            atkinsonIndexRealSlope u x)) := hdiv
      _ = (2 * Real.pi * (t - u) / x) /
          (atkinsonIndexRealSlope t x +
            atkinsonIndexRealSlope u x) := by
        field_simp [hx.ne', hsumPos.ne']
  · unfold atkinsonIndexFirstDerivativeUpper
    have hdiv := div_le_div_of_nonneg_left hnum hdenLowerPos hdenLower
    calc
      (2 * Real.pi * (t - u) / x) /
          (atkinsonIndexRealSlope t x +
            atkinsonIndexRealSlope u x) =
          (2 * Real.pi * (t - u)) /
            (x * (atkinsonIndexRealSlope t x +
              atkinsonIndexRealSlope u x)) := by
        field_simp [hx.ne', hsumPos.ne']
      _ ≤ (2 * Real.pi * (t - u)) /
          (A * (2 * atkinsonIndexSlopeLower u B)) := hdiv
      _ = Real.pi * (t - u) /
          (A * atkinsonIndexSlopeLower u B) := by ring

/-- The positively sloped orientation of the natural-index phase
difference. -/
def atkinsonIndexIncreasingDifferenceNat
    (t u : ℝ) (K n : ℕ) : ℝ :=
  atkinsonSourcePhase t (K + n) -
    atkinsonSourcePhase u (K + n)

/-- A unit increment of the exact phase difference equals its derivative at
an intermediate real index. -/
theorem exists_atkinsonIndexIncreasingDifferenceNat_increment
    {t u : ℝ} {K n : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K) :
    ∃ xi ∈ Set.Ioo ((K + n : ℕ) : ℝ) ((K + n + 1 : ℕ) : ℝ),
      atkinsonIndexRealSlope t xi -
          atkinsonIndexRealSlope u xi =
        atkinsonIndexIncreasingDifferenceNat t u K (n + 1) -
          atkinsonIndexIncreasingDifferenceNat t u K n := by
  let F : ℝ → ℝ := atkinsonIndexPhaseDifference t u
  let F' : ℝ → ℝ := fun x =>
    atkinsonIndexRealSlope t x - atkinsonIndexRealSlope u x
  have hleft : 0 < ((K + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < K + n by omega)
  have hlt : ((K + n : ℕ) : ℝ) < ((K + n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show K + n < K + n + 1 by omega)
  have hcont : ContinuousOn F
      (Set.Icc ((K + n : ℕ) : ℝ) ((K + n + 1 : ℕ) : ℝ)) := by
    intro x hx
    exact (hasDerivAt_atkinsonIndexPhaseDifference
      (hu.trans htu) hu (hleft.trans_le hx.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo ((K + n : ℕ) : ℝ)
      ((K + n + 1 : ℕ) : ℝ), HasDerivAt F (F' x) x := by
    intro x hx
    exact hasDerivAt_atkinsonIndexPhaseDifference
      (hu.trans htu) hu (hleft.trans hx.1)
  obtain ⟨xi, hxi, heq⟩ :=
    exists_hasDerivAt_eq_slope F F' hlt hcont hderiv
  refine ⟨xi, hxi, ?_⟩
  dsimp only [F, F'] at heq ⊢
  have hone : (((K + n + 1 : ℕ) : ℝ) - ((K + n : ℕ) : ℝ)) = 1 := by
    push_cast
    ring
  rw [hone, div_one] at heq
  simp only [atkinsonIndexPhaseDifference] at heq
  unfold atkinsonIndexIncreasingDifferenceNat
  rw [← atkinsonIndexRealPhase_natCast,
    ← atkinsonIndexRealPhase_natCast,
    ← atkinsonIndexRealPhase_natCast,
    ← atkinsonIndexRealPhase_natCast]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using heq

/-- Uniform unit-increment bounds obtained from the pointwise derivative
estimate. -/
theorem atkinsonIndexIncreasingDifferenceNat_increment_bounds
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((K + N + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ∀ n ≤ N,
      atkinsonIndexFirstDerivativeLower u t K (K + N + 1) ≤
          atkinsonIndexIncreasingDifferenceNat t u K (n + 1) -
            atkinsonIndexIncreasingDifferenceNat t u K n ∧
        atkinsonIndexIncreasingDifferenceNat t u K (n + 1) -
            atkinsonIndexIncreasingDifferenceNat t u K n ≤
          atkinsonIndexFirstDerivativeUpper u t K (K + N + 1) := by
  intro n hn
  obtain ⟨xi, hxi, heq⟩ :=
    exists_atkinsonIndexIncreasingDifferenceNat_increment hu htu hK
      (K := K) (n := n)
  have hAxi : (K : ℝ) ≤ xi := by
    have hKle : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right K n
    exact hKle.trans hxi.1.le
  have hxiB : xi ≤ ((K + N + 1 : ℕ) : ℝ) := by
    have hcast : ((K + n + 1 : ℕ) : ℝ) ≤
        ((K + N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show K + n + 1 ≤ K + N + 1 by omega)
    exact hxi.2.le.trans hcast
  have hBu : ((K + N + 1 : ℕ) : ℝ) ≤ u := by
    exact_mod_cast hblock.trans' (by
      exact_mod_cast (show K + N + 1 ≤ K + N + 2 by omega))
  have hb := atkinsonIndexRealSlopeDifference_box_bounds
    hu htu (by exact_mod_cast hK) hAxi hxiB hBu htUpper
  rw [heq] at hb
  simpa only [Nat.cast_add, Nat.cast_one] using hb

/-- The unit increments of the positively sloped phase orientation decrease
with the summation index. -/
theorem atkinsonIndexIncreasingDifferenceNat_increment_anti
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((K + N + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ∀ n < N,
      atkinsonIndexIncreasingDifferenceNat t u K (n + 2) -
          atkinsonIndexIncreasingDifferenceNat t u K (n + 1) ≤
        atkinsonIndexIncreasingDifferenceNat t u K (n + 1) -
          atkinsonIndexIncreasingDifferenceNat t u K n := by
  intro n hn
  have hsecond :=
    (atkinsonIndexPositiveDifferenceNat_secondDifference_bounds
      hu htu hK hblock htUpper n hn).1
  have hlam := atkinsonIndexBProcessLambda_pos
    (N := N) hu htu hK
  unfold atkinsonIndexPositiveDifferenceNat at hsecond
  unfold atkinsonIndexIncreasingDifferenceNat
  linarith

/-- The first-derivative form of Kusmin--Landau for the exact phase
difference.  The upper-scale hypothesis is the source's small-frequency
case; it keeps every period-endpoint condition explicit. -/
theorem atkinsonIndexIncreasingDifference_KL
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((K + N + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u)
    (hsmall :
      atkinsonIndexFirstDerivativeUpper u t K (K + N + 1) ≤
        Real.pi) :
    ‖∑ n ∈ Finset.range (N + 1),
        RiemannZeta.GuthMaynard.unitaryPhase
          (atkinsonIndexIncreasingDifferenceNat t u K n)‖ ≤
      2 * Real.pi /
        atkinsonIndexFirstDerivativeLower u t K (K + N + 1) := by
  let δ := atkinsonIndexFirstDerivativeLower u t K (K + N + 1)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hBreal : 0 < ((K + N + 1 : ℕ) : ℝ) := by positivity
  have hBexpr : 0 < (K : ℝ) + (N : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hBreal
  have hδ : 0 < δ := by
    unfold δ atkinsonIndexFirstDerivativeLower
    exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr htu))
      (mul_pos hBexpr (atkinsonIndexSlopeUpper_pos hu hKreal))
  have hb := atkinsonIndexIncreasingDifferenceNat_increment_bounds
    hu htu hK hblock htUpper
  have hδpi : δ ≤ Real.pi := by
    exact (hb 0 (Nat.zero_le N)).1.trans
      ((hb 0 (Nat.zero_le N)).2.trans hsmall)
  apply RiemannZeta.GuthMaynard.kusminLandau_one_period_decreasing
      (atkinsonIndexIncreasingDifferenceNat t u K) N δ hδ
  · intro n hn
    exact (hb n hn).1
  · intro n hn
    have hupp := (hb n hn).2.trans hsmall
    linarith
  · exact atkinsonIndexIncreasingDifferenceNat_increment_anti
      hu htu hK hblock htUpper


end

end MathCollab.Density.Stronger.Atkinson
