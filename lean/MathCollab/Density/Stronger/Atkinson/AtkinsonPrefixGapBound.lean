module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixCancellation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Explicit, orientation-free bounds for actual truncated Gram sums

Take the minimum of the proved triangle bound, B-process bound, and
the first-derivative alternative where its exact half-period condition
holds. The diagonal is the literal prefix length.
-/

set_option autoImplicit false
noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace MathCollab.Density.Stronger.Atkinson

theorem norm_atkinsonPrefixGram_le_length (M j : ℕ) (t u : ℝ) :
    ‖atkinsonPrefixGram M j t u‖ ≤ (j:ℝ) := by
  unfold atkinsonPrefixGram
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        ‖unitaryPhase (atkinsonSourcePhase u (M+i)-atkinsonSourcePhase t (M+i))‖ :=
      norm_sum_le _ _
    _ = _ := by simp

theorem atkinsonPrefixGramMax_le_length (M N : ℕ) (t u : ℝ) :
    atkinsonPrefixGramMax M N t u ≤ (N:ℝ) := by
  unfold atkinsonPrefixGramMax
  apply Finset.sup'_le
  intro j hj
  exact (norm_atkinsonPrefixGram_le_length M j t u).trans
    (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj))

def atkinsonOrderedPrefixGapMajorant (M N : ℕ) (t u : ℝ) : ℝ :=
  min (N:ℝ)
    (if atkinsonIndexFirstDerivativeUpper u t M ((M:ℝ)+(N:ℝ)+1) ≤ Real.pi then
      min (atkinsonPrefixBProcessMajorant M N t u)
        (atkinsonPrefixFirstDerivativeMajorant M N t u)
    else atkinsonPrefixBProcessMajorant M N t u)

def atkinsonPrefixGapMajorant (M N : ℕ) (t u : ℝ) : ℝ :=
  if t = u then (N:ℝ)
  else atkinsonOrderedPrefixGapMajorant M N (max t u) (min t u)

theorem atkinsonPrefixGramMax_le_orderedGap {M N : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ u) (htUpper : t ≤ 2*u) :
    atkinsonPrefixGramMax M N t u ≤ atkinsonOrderedPrefixGapMajorant M N t u := by
  have hb := atkinsonPrefixGramMax_le_bProcess hu htu hM hblock htUpper
  have hl := atkinsonPrefixGramMax_le_length M N t u
  unfold atkinsonOrderedPrefixGapMajorant
  apply le_min hl
  split_ifs with hsmall
  · exact le_min hb (atkinsonPrefixGramMax_le_firstDerivative hu htu hM hblock htUpper hsmall)
  · exact hb

theorem atkinsonPrefixGapMajorant_self (M N : ℕ) (t : ℝ) :
    atkinsonPrefixGapMajorant M N t t = (N:ℝ) := by
  simp [atkinsonPrefixGapMajorant]

theorem atkinsonPrefixGapMajorant_swap (M N : ℕ) (t u : ℝ) :
    atkinsonPrefixGapMajorant M N u t = atkinsonPrefixGapMajorant M N t u := by
  simp only [atkinsonPrefixGapMajorant,eq_comm,max_comm,min_comm]

theorem atkinsonPrefixGramMax_le_gap {M N : ℕ} {t u : ℝ}
    (hu : 0 < min t u) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ min t u) (htUpper : max t u ≤ 2*min t u) :
    atkinsonPrefixGramMax M N t u ≤ atkinsonPrefixGapMajorant M N t u := by
  by_cases he : t = u
  · subst u
    rw [atkinsonPrefixGramMax_self,atkinsonPrefixGapMajorant_self]
  · unfold atkinsonPrefixGapMajorant
    rw [ite_eq_right he]
    rcases lt_or_gt_of_ne he with htu | hut
    · simp only [max_eq_right htu.le,min_eq_left htu.le] at hu hblock htUpper ⊢
      rw [atkinsonPrefixGramMax_swap M N u t]
      exact atkinsonPrefixGramMax_le_orderedGap hu htu hM hblock htUpper
    · simp only [max_eq_left hut.le,min_eq_right hut.le] at hu hblock htUpper ⊢
      exact atkinsonPrefixGramMax_le_orderedGap hu hut hM hblock htUpper

theorem atkinsonPrefixGapMajorant_nonneg {M N : ℕ} {t u : ℝ}
    (hu : 0 < min t u) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ min t u) (htUpper : max t u ≤ 2*min t u) :
    0 ≤ atkinsonPrefixGapMajorant M N t u :=
  (atkinsonPrefixGramMax_nonneg M N t u).trans
    (atkinsonPrefixGramMax_le_gap hu hM hblock htUpper)

theorem norm_atkinsonPrefixGram_le_gap {M N j : ℕ} {t u : ℝ}
    (hu : 0 < min t u) (hM : 0 < M)
    (hblock : ((M+N+2:ℕ):ℝ) ≤ min t u) (htUpper : max t u ≤ 2*min t u) (hj : j ≤ N) :
    ‖atkinsonPrefixGram M j t u‖ ≤ atkinsonPrefixGapMajorant M N t u :=
  (norm_atkinsonPrefixGram_le_max M N j hj t u).trans
    (atkinsonPrefixGramMax_le_gap hu hM hblock htUpper)

end MathCollab.Density.Stronger.Atkinson
