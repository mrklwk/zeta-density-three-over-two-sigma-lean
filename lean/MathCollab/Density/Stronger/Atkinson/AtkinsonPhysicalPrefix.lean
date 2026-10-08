module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFarGap
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPhysicalCutoff

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- Actual source-cutoff dyadic prefixes have the explicit near-gap estimate.
The threshold precedes every physical height, width, block and prefix. -/
theorem exists_norm_physical_atkinsonPrefixGram_le_near {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      ∀ k : ℕ, k < Nat.clog 2 (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) →
      ∀ j : ℕ, j ≤ 2^k → ∀ t u : ℝ,
      H ≤ t → t ≤ 2*H → H ≤ u → u ≤ 2*H → t ≠ u →
      |t-u| ≤ Real.sqrt (H*((2^k:ℕ):ℝ)) →
      ‖atkinsonPrefixGram (2^k) j t u‖ ≤
        60*Real.sqrt (H*((2^k:ℕ):ℝ))/|t-u| := by
  obtain ⟨H₀, hH₀, hgram⟩ := exists_atkinsonPhysicalPrefixGramMax_le_gap hδ
  refine ⟨H₀, hH₀, ?_⟩
  intro H G hH hG k hk j hj t u ht htU hu huU hne hgap
  have hHpos : 0 < H := by linarith
  exact ((norm_atkinsonPrefixGram_le_max (2^k) (2^k) j hj t u).trans
    (hgram H G hH hG k hk t u ht htU hu huU)).trans
      (atkinsonPrefixGapMajorant_le_near hHpos ht htU hu huU hne
        (pow_pos (by norm_num) _) hgap)

/-- Actual source-cutoff dyadic prefixes have the explicit far-gap estimate,
for both height orders and every prefix, including the empty prefix. -/
theorem exists_norm_physical_atkinsonPrefixGram_le_far {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      ∀ k : ℕ, k < Nat.clog 2 (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) →
      ∀ j : ℕ, j ≤ 2^k → ∀ t u : ℝ,
      H ≤ t → t ≤ 2*H → H ≤ u → u ≤ 2*H →
      Real.sqrt (H*((2^k:ℕ):ℝ)) ≤ |t-u| →
      ‖atkinsonPrefixGram (2^k) j t u‖ ≤
        2000*Real.sqrt (((2^k:ℕ):ℝ)*|t-u|/Real.sqrt (H*((2^k:ℕ):ℝ))) := by
  obtain ⟨H₀, hH₀, hgram⟩ := exists_atkinsonPhysicalPrefixGramMax_le_gap hδ
  refine ⟨H₀, hH₀, ?_⟩
  intro H G hH hG k hk j hj t u ht htU hu huU hgap
  have hHpos : 0 < H := by linarith
  exact ((norm_atkinsonPrefixGram_le_max (2^k) (2^k) j hj t u).trans
    (hgram H G hH hG k hk t u ht htU hu huU)).trans
      (atkinsonPrefixGapMajorant_le_far hHpos ht htU hu huU
        (pow_pos (by norm_num) _) hgap)

end MathCollab.Density.Stronger.Atkinson
