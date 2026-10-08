module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixMax

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Cancellation for every prefix of the actual source Gram entry

The full ambient block supplies one pair of curvature parameters and one
first-derivative scale. Restricting the increment estimates proves the
bounds for every shorter prefix, including zero, without a common
maximizer or a terminal-block substitution.
-/

set_option autoImplicit false
noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonPrefixBProcessMajorant (M N : ℕ) (t u : ℝ) : ℝ :=
  ((N:ℝ)*atkinsonIndexBProcessLambdaUpper t u M N/(2*Real.pi)+2)*
    (2*Real.pi/Real.sqrt (atkinsonIndexBProcessLambda t u M N)+
      2*(Real.sqrt (atkinsonIndexBProcessLambda t u M N)/
        atkinsonIndexBProcessLambda t u M N+1))

theorem atkinsonIndexBProcessLambdaUpper_pos {M N : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M) :
    0 < atkinsonIndexBProcessLambdaUpper t u M N := by
  unfold atkinsonIndexBProcessLambdaUpper atkinsonIndexBoxCurvatureUpper
  exact mul_pos
    (div_pos Real.pi_pos (mul_pos (sq_pos_of_pos (by exact_mod_cast hM))
      (atkinsonIndexSlopeLower_pos hu (by
        exact_mod_cast (show 0 < M+N+2 by omega)))))
    (sub_pos.mpr htu)

theorem atkinsonPrefixBProcessMajorant_nonneg {M N : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M) :
    0 ≤ atkinsonPrefixBProcessMajorant M N t u := by
  have hl := atkinsonIndexBProcessLambda_pos (N := N) hu htu hM
  have hU := atkinsonIndexBProcessLambdaUpper_pos (N := N) hu htu hM
  unfold atkinsonPrefixBProcessMajorant
  positivity

theorem norm_atkinsonPrefixGram_le_bProcess {M N j : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ u) (htUpper : t ≤ 2*u) (hj : j ≤ N) :
    ‖atkinsonPrefixGram M j t u‖ ≤ atkinsonPrefixBProcessMajorant M N t u := by
  have hl := atkinsonIndexBProcessLambda_pos (N := N) hu htu hM
  have hU := atkinsonIndexBProcessLambdaUpper_pos (N := N) hu htu hM
  have hb := atkinsonIndexPositiveDifferenceNat_secondDifference_bounds hu htu hM hblock htUpper
  cases j with
  | zero =>
      simpa [atkinsonPrefixGram] using atkinsonPrefixBProcessMajorant_nonneg (N := N) hu htu hM
  | succ k =>
      have hraw := vanDerCorput_B_process (atkinsonIndexPositiveDifferenceNat t u M) k
        (atkinsonIndexBProcessLambda t u M N) (atkinsonIndexBProcessLambdaUpper t u M N) hl
        (fun n hn => (hb n (by omega)).1) (fun n hn => (hb n (by omega)).2)
      change ‖atkinsonPrefixGram M (k+1) t u‖ ≤ _ at hraw
      apply hraw.trans
      unfold atkinsonPrefixBProcessMajorant
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hk : (k:ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
      have hm := mul_le_mul_of_nonneg_right hk hU.le
      have hd := div_le_div_of_nonneg_right hm (by positivity : 0 ≤ 2*Real.pi)
      linarith

theorem atkinsonPrefixGramMax_le_bProcess {M N : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ u) (htUpper : t ≤ 2*u) :
    atkinsonPrefixGramMax M N t u ≤ atkinsonPrefixBProcessMajorant M N t u := by
  unfold atkinsonPrefixGramMax
  apply Finset.sup'_le
  intro j hj
  exact norm_atkinsonPrefixGram_le_bProcess hu htu hM hblock htUpper
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

def atkinsonPrefixFirstDerivativeMajorant (M N : ℕ) (t u : ℝ) : ℝ :=
  2*Real.pi/atkinsonIndexFirstDerivativeLower u t M ((M:ℝ)+(N:ℝ)+1)

theorem atkinsonPrefixFirstDerivativeMajorant_pos {M N : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M) :
    0 < atkinsonPrefixFirstDerivativeMajorant M N t u := by
  unfold atkinsonPrefixFirstDerivativeMajorant atkinsonIndexFirstDerivativeLower
  exact div_pos (by positivity)
    (div_pos (mul_pos Real.pi_pos (sub_pos.mpr htu))
      (mul_pos (by exact_mod_cast (show 0 < M+N+1 by omega))
        (atkinsonIndexSlopeUpper_pos hu (by exact_mod_cast hM))))

theorem norm_atkinsonPrefixGram_le_firstDerivative {M N j : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ u) (htUpper : t ≤ 2*u)
    (hsmall : atkinsonIndexFirstDerivativeUpper u t M ((M:ℝ)+(N:ℝ)+1) ≤ Real.pi)
    (hj : j ≤ N) :
    ‖atkinsonPrefixGram M j t u‖ ≤ atkinsonPrefixFirstDerivativeMajorant M N t u := by
  let δ := atkinsonIndexFirstDerivativeLower u t M ((M:ℝ)+(N:ℝ)+1)
  have hδ : 0 < δ := by
    unfold δ atkinsonIndexFirstDerivativeLower
    exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr htu))
      (mul_pos (by exact_mod_cast (show 0 < M+N+1 by omega))
        (atkinsonIndexSlopeUpper_pos hu (by exact_mod_cast hM)))
  have hb := atkinsonIndexIncreasingDifferenceNat_increment_bounds hu htu hM hblock htUpper
  have hm := atkinsonIndexIncreasingDifferenceNat_increment_anti hu htu hM hblock htUpper
  have hδpi : δ ≤ Real.pi := (hb 0 (Nat.zero_le N)).1.trans
    ((hb 0 (Nat.zero_le N)).2.trans hsmall)
  cases j with
  | zero =>
      simpa [atkinsonPrefixGram] using
        (atkinsonPrefixFirstDerivativeMajorant_pos (N := N) hu htu hM).le
  | succ k =>
      have hraw := kusminLandau_one_period_decreasing
        (atkinsonIndexIncreasingDifferenceNat t u M) k δ hδ
        (fun n hn => (hb n (by omega)).1)
        (fun n hn => by
          have h := (hb n (by omega)).2.trans hsmall
          linarith)
        (fun n hn => hm n (by omega))
      change ‖atkinsonPrefixGram M (k+1) u t‖ ≤ _ at hraw
      rw [atkinsonPrefixGram_swap,Complex.norm_conj] at hraw
      exact hraw

theorem atkinsonPrefixGramMax_le_firstDerivative {M N : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ u) (htUpper : t ≤ 2*u)
    (hsmall : atkinsonIndexFirstDerivativeUpper u t M ((M:ℝ)+(N:ℝ)+1) ≤ Real.pi) :
    atkinsonPrefixGramMax M N t u ≤ atkinsonPrefixFirstDerivativeMajorant M N t u := by
  unfold atkinsonPrefixGramMax
  apply Finset.sup'_le
  intro j hj
  exact norm_atkinsonPrefixGram_le_firstDerivative hu htu hM hblock htUpper hsmall
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem atkinsonPrefixFirstDerivativeMajorant_eq_gap {M N : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M) :
    atkinsonPrefixFirstDerivativeMajorant M N t u =
      2*((M:ℝ)+(N:ℝ)+1)*atkinsonIndexSlopeUpper u M/(t-u) := by
  have hs := atkinsonIndexSlopeUpper_pos (x := (M:ℝ)) hu (by exact_mod_cast hM)
  have hB : (0:ℝ) < (M:ℝ)+(N:ℝ)+1 := by positivity
  unfold atkinsonPrefixFirstDerivativeMajorant atkinsonIndexFirstDerivativeLower
  field_simp [Real.pi_ne_zero,hs.ne',hB.ne',sub_ne_zero.mpr htu.ne']

end MathCollab.Density.Stronger.Atkinson
