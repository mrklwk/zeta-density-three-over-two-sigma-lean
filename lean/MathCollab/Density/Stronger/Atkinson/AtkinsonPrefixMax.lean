module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixVectors

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonPrefixGramMax (m N : ℕ) (t u : ℝ) : ℝ :=
  (Finset.range (N+1)).sup' (by simp) (fun j => ‖atkinsonPrefixGram m j t u‖)

theorem norm_atkinsonPrefixGram_le_max (m N j : ℕ) (hj : j ≤ N) (t u : ℝ) :
    ‖atkinsonPrefixGram m j t u‖ ≤ atkinsonPrefixGramMax m N t u := by
  unfold atkinsonPrefixGramMax
  exact Finset.le_sup' (fun k => ‖atkinsonPrefixGram m k t u‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem atkinsonPrefixGramMax_nonneg (m N : ℕ) (t u : ℝ) :
    0 ≤ atkinsonPrefixGramMax m N t u := by
  have h := norm_atkinsonPrefixGram_le_max m N 0 (Nat.zero_le N) t u
  simpa [atkinsonPrefixGram] using h

theorem atkinsonPrefixGramMax_self (m N : ℕ) (t : ℝ) :
    atkinsonPrefixGramMax m N t t = (N:ℝ) := by
  apply le_antisymm
  · unfold atkinsonPrefixGramMax
    apply Finset.sup'_le
    intro j hj
    rw [norm_atkinsonPrefixGram_self]
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  · simpa only [norm_atkinsonPrefixGram_self] using
      norm_atkinsonPrefixGram_le_max m N N le_rfl t t

theorem atkinsonPrefixGramMax_swap (m N : ℕ) (t u : ℝ) :
    atkinsonPrefixGramMax m N u t = atkinsonPrefixGramMax m N t u := by
  unfold atkinsonPrefixGramMax
  simp_rw [atkinsonPrefixGram_swap m _ u t,Complex.norm_conj]


end MathCollab.Density.Stronger.Atkinson
