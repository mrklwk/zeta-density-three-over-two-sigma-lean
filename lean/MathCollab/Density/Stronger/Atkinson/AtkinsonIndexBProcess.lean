module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexScales
public import GuthMaynard.SecondOrderMeanValue
public import GuthMaynard.SecondDerivative

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonBProcess` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# The B-process for a difference of Atkinson phases

This file passes the exact equation-(11) phase difference to the native
second-derivative van der Corput theorem.  The lower and upper curvature
parameters are explicit functions of the physical height gap and index box.
-/

open Set
open RiemannZeta.GuthMaynard

namespace MathCollab.Density.Stronger.Atkinson

set_option autoImplicit false
noncomputable section

/-- Orient the two-height phase difference so that its second derivative is
positive when `u < t`. -/
def atkinsonIndexPositiveDifference (t u x : ℝ) : ℝ :=
  atkinsonIndexRealPhase u x - atkinsonIndexRealPhase t x

theorem hasDerivAt_atkinsonIndexPositiveDifference
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (atkinsonIndexPositiveDifference t u)
      (atkinsonIndexRealSlope u x -
        atkinsonIndexRealSlope t x) x := by
  unfold atkinsonIndexPositiveDifference atkinsonIndexRealSlope
  exact (hasDerivAt_atkinsonIndexRealPhase hu hx).sub
    (hasDerivAt_atkinsonIndexRealPhase ht hx)

theorem hasDerivAt_atkinsonIndexPositiveDifferenceSlope
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt
      (fun y => atkinsonIndexRealSlope u y -
        atkinsonIndexRealSlope t y)
      (atkinsonIndexRealCurvature u x -
        atkinsonIndexRealCurvature t x) x :=
  (hasDerivAt_atkinsonIndexRealSlope hu hx).sub
    (hasDerivAt_atkinsonIndexRealSlope ht hx)

/-- Exact second-order mean-value identity for the positively oriented phase
difference. -/
theorem exists_atkinsonIndexPositiveDifference_secondDifference
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    ∃ xi ∈ Set.Ioo x (x + 2),
      atkinsonIndexRealCurvature u xi -
          atkinsonIndexRealCurvature t xi =
        (atkinsonIndexPositiveDifference t u (x + 2) -
          atkinsonIndexPositiveDifference t u (x + 1)) -
        (atkinsonIndexPositiveDifference t u (x + 1) -
          atkinsonIndexPositiveDifference t u x) := by
  let F : ℝ → ℝ := atkinsonIndexPositiveDifference t u
  let F' : ℝ → ℝ := fun y =>
    atkinsonIndexRealSlope u y - atkinsonIndexRealSlope t y
  let F'' : ℝ → ℝ := fun y =>
    atkinsonIndexRealCurvature u y -
      atkinsonIndexRealCurvature t y
  have hmv := second_order_mean_value F F' F'' x
    (fun y hy => by
      dsimp only [F, F']
      exact hasDerivAt_atkinsonIndexPositiveDifference ht hu
        (hx.trans_le hy.1))
    (fun y hy => by
      dsimp only [F', F'']
      exact hasDerivAt_atkinsonIndexPositiveDifferenceSlope ht hu
        (hx.trans_le hy.1))
  obtain ⟨xi, hxi, heq⟩ := hmv
  refine ⟨xi, hxi, ?_⟩
  dsimp only [F, F''] at heq ⊢
  calc
    _ = F (x + 2) - 2 * F (x + 1) + F x := heq
    _ = (F (x + 2) - F (x + 1)) -
        (F (x + 1) - F x) := by ring

/-- The natural-index phase used by the finite B-process. -/
def atkinsonIndexPositiveDifferenceNat
    (t u : ℝ) (K n : ℕ) : ℝ :=
  atkinsonSourcePhase u (K + n) -
    atkinsonSourcePhase t (K + n)

/-- The real and natural versions of the positively oriented phase agree at
natural indices. -/
theorem atkinsonIndexPositiveDifference_natCast
    (t u : ℝ) (K n : ℕ) :
    atkinsonIndexPositiveDifference t u (K + n : ℕ) =
      atkinsonIndexPositiveDifferenceNat t u K n := by
  unfold atkinsonIndexPositiveDifference
    atkinsonIndexPositiveDifferenceNat
  rw [atkinsonIndexRealPhase_natCast,
    atkinsonIndexRealPhase_natCast]

/-- Explicit lower curvature parameter for a block `K <= K+n <= K+N+2`. -/
def atkinsonIndexBProcessLambda
    (t u : ℝ) (K N : ℕ) : ℝ :=
  atkinsonIndexBoxCurvatureLower u K (K + N + 2) * (t - u)

/-- Explicit upper curvature parameter for the same block. -/
def atkinsonIndexBProcessLambdaUpper
    (t u : ℝ) (K N : ℕ) : ℝ :=
  atkinsonIndexBoxCurvatureUpper u K (K + N + 2) * (t - u)

theorem atkinsonIndexBProcessLambda_pos
    {t u : ℝ} {K N : ℕ} (hu : 0 < u) (htu : u < t) (hK : 0 < K) :
    0 < atkinsonIndexBProcessLambda t u K N := by
  unfold atkinsonIndexBProcessLambda
    atkinsonIndexBoxCurvatureLower
  have hB : 0 < (K + N + 2 : ℕ) := by omega
  exact mul_pos
    (div_pos Real.pi_pos
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by exact_mod_cast hB)))
        (atkinsonIndexSlopeUpper_pos hu (by exact_mod_cast hK))))
    (sub_pos.mpr htu)

/-- Every unit-spaced second difference of the exact natural phase is
bounded by the explicit dyadic curvature parameters. -/
theorem atkinsonIndexPositiveDifferenceNat_secondDifference_bounds
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : ((K + N + 2 : ℕ) : ℝ) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ∀ n, n < N →
      atkinsonIndexBProcessLambda t u K N ≤
          (atkinsonIndexPositiveDifferenceNat t u K (n + 2) -
            atkinsonIndexPositiveDifferenceNat t u K (n + 1)) -
          (atkinsonIndexPositiveDifferenceNat t u K (n + 1) -
            atkinsonIndexPositiveDifferenceNat t u K n) ∧
        (atkinsonIndexPositiveDifferenceNat t u K (n + 2) -
            atkinsonIndexPositiveDifferenceNat t u K (n + 1)) -
          (atkinsonIndexPositiveDifferenceNat t u K (n + 1) -
            atkinsonIndexPositiveDifferenceNat t u K n) ≤
        atkinsonIndexBProcessLambdaUpper t u K N := by
  intro n hn
  have ht : 0 < t := hu.trans htu
  have hx : 0 < ((K + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < K + n by omega)
  obtain ⟨xi, hxi, heq⟩ :=
    exists_atkinsonIndexPositiveDifference_secondDifference ht hu hx
  have hAxi : (K : ℝ) ≤ xi := by
    have : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right K n
    exact this.trans hxi.1.le
  have hxiB : xi ≤ ((K + N + 2 : ℕ) : ℝ) := by
    have hncast : ((K + n : ℕ) : ℝ) + 2 ≤
        ((K + N + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show K + n + 2 ≤ K + N + 2 by omega)
    exact hxi.2.le.trans hncast
  have hbox := atkinsonIndexCurvatureDerivative_box_bounds hu
    (by exact_mod_cast hK) hAxi hxiB
  have hpoint := atkinsonIndexCurvatureDifference_bounds hu htu
    (hx.trans hxi.1) (hxiB.trans hblock) htUpper
  have hgap : 0 ≤ t - u := sub_nonneg.mpr htu.le
  have hlower := (mul_le_mul_of_nonneg_right hbox.1 hgap).trans hpoint.1
  have hupper := hpoint.2.trans (mul_le_mul_of_nonneg_right hbox.2 hgap)
  have heqNat :
      atkinsonIndexRealCurvature u xi -
          atkinsonIndexRealCurvature t xi =
        (atkinsonIndexPositiveDifferenceNat t u K (n + 2) -
          atkinsonIndexPositiveDifferenceNat t u K (n + 1)) -
        (atkinsonIndexPositiveDifferenceNat t u K (n + 1) -
          atkinsonIndexPositiveDifferenceNat t u K n) := by
    have htwo : ((K + n : ℕ) : ℝ) + 2 = ((K + (n + 2) : ℕ) : ℝ) := by
      push_cast
      ring
    have hone : ((K + n : ℕ) : ℝ) + 1 = ((K + (n + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    calc
      _ = (atkinsonIndexPositiveDifference t u
              (((K + (n + 2) : ℕ) : ℝ)) -
            atkinsonIndexPositiveDifference t u
              (((K + (n + 1) : ℕ) : ℝ))) -
          (atkinsonIndexPositiveDifference t u
              (((K + (n + 1) : ℕ) : ℝ)) -
            atkinsonIndexPositiveDifference t u
              (((K + n : ℕ) : ℝ))) := by
          rw [heq, htwo, hone]
      _ = _ := by
        simp only [atkinsonIndexPositiveDifference_natCast]
  unfold atkinsonIndexBProcessLambda
    atkinsonIndexBProcessLambdaUpper
  rw [show -(atkinsonIndexRealCurvature t xi -
      atkinsonIndexRealCurvature u xi) =
      atkinsonIndexRealCurvature u xi -
        atkinsonIndexRealCurvature t xi by ring] at hlower hupper
  rw [heqNat] at hlower hupper
  push_cast at hlower hupper ⊢
  have hpair := And.intro hlower hupper
  simpa only [add_assoc] using hpair

/-- The native van der Corput B-process applied to the exact two-height
Atkinson phase. -/
theorem atkinsonIndexPositiveDifference_B_process
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : ((K + N + 2 : ℕ) : ℝ) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ‖∑ n ∈ Finset.range (N + 1),
        unitaryPhase (atkinsonIndexPositiveDifferenceNat t u K n)‖ ≤
      ((N : ℝ) * atkinsonIndexBProcessLambdaUpper t u K N /
          (2 * Real.pi) + 2) *
        (2 * Real.pi /
            Real.sqrt (atkinsonIndexBProcessLambda t u K N) +
          2 * (Real.sqrt (atkinsonIndexBProcessLambda t u K N) /
            atkinsonIndexBProcessLambda t u K N + 1)) := by
  apply vanDerCorput_B_process
  · exact atkinsonIndexBProcessLambda_pos hu htu hK
  · intro n hn
    exact (atkinsonIndexPositiveDifferenceNat_secondDifference_bounds
      hu htu hK hblock htUpper n hn).1
  · intro n hn
    exact (atkinsonIndexPositiveDifferenceNat_secondDifference_bounds
      hu htu hK hblock htUpper n hn).2


end

end MathCollab.Density.Stronger.Atkinson
