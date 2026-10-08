module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_WEIGHT_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.TruncatedDyadicPartition
public import MathCollab.Density.Stronger.Atkinson.AtkinsonDyadicGramBudget

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonDyadicPhaseBound (T G : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.clog 2 N),
    ((2^j:ℕ):ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*((2^j:ℕ):ℝ))/(12*T))*
      atkinsonPhaseBlockMax T (2^j) (truncatedDyadicLength N j)

theorem atkinsonDyadicPhaseBound_nonneg (T G : ℝ) (N : ℕ) :
    0 ≤ atkinsonDyadicPhaseBound T G N := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.exp_pos _).le) (atkinsonPhaseBlockMax_nonneg _ _ _)

theorem atkinsonPhaseBlockMax_mono (T : ℝ) (m : ℕ) {N K : ℕ} (hNK : N ≤ K) :
    atkinsonPhaseBlockMax T m N ≤ atkinsonPhaseBlockMax T m K := by
  conv_lhs => unfold atkinsonPhaseBlockMax
  apply Finset.sup'_le
  intro j hj
  exact norm_atkinsonPhaseBlockSum_le_max T m K j
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hNK)

/-- Full raw phase-prefix maxima may enlarge the last block; the stationary
source and its small-frequency geometry are not enlarged. -/
def atkinsonFullDyadicPhaseBound (T G : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.clog 2 N),
    ((2^j:ℕ):ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*((2^j:ℕ):ℝ))/(12*T))*
      atkinsonPhaseBlockMax T (2^j) (2^j)

theorem atkinsonFullDyadicPhaseBound_nonneg (T G : ℝ) (N : ℕ) :
    0 ≤ atkinsonFullDyadicPhaseBound T G N := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.exp_pos _).le) (atkinsonPhaseBlockMax_nonneg _ _ _)

theorem atkinsonDyadicPhaseBound_le_full (T G : ℝ) (N : ℕ) :
    atkinsonDyadicPhaseBound T G N ≤ atkinsonFullDyadicPhaseBound T G N := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (atkinsonPhaseBlockMax_mono T (2^j) (truncatedDyadicLength_le_width N j))
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le)

theorem atkinsonFullDyadicPhaseBound_le_undamped {T : ℝ} (hT : 0 < T) (G : ℝ) (N : ℕ) :
    atkinsonFullDyadicPhaseBound T G N ≤ atkinsonUndampedDyadicPhaseBound T N := by
  apply Finset.sum_le_sum
  intro j _
  have he : Real.exp (-(G^2*((2^j:ℕ):ℝ))/(12*T)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg G) (Nat.cast_nonneg _)))
      (by positivity)
  calc
    _ ≤ (((2^j:ℕ):ℝ)^(-(1/4:ℝ))*1)*atkinsonPhaseBlockMax T (2^j) (2^j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (atkinsonPhaseBlockMax_nonneg _ _ _)
    _ = _ := by rw [mul_one]

end MathCollab.Density.Stronger.Atkinson
