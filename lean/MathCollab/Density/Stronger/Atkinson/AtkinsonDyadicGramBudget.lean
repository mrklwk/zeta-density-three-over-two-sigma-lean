module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCoefficientEnergy
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPhysicalCutoff

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonUndampedDyadicPhaseBound (T : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.clog 2 N),
    ((2^j:ℕ):ℝ)^(-(1/4:ℝ))*atkinsonPhaseBlockMax T (2^j) (2^j)

theorem atkinsonUndampedDyadicPhaseBound_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ atkinsonUndampedDyadicPhaseBound T N := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (atkinsonPhaseBlockMax_nonneg _ _ _))

theorem atkinsonUndampedDyadicPhaseBound_mono (T : ℝ) {N K : ℕ} (hNK : N ≤ K) :
    atkinsonUndampedDyadicPhaseBound T N ≤ atkinsonUndampedDyadicPhaseBound T K := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.clog_mono_right 2 hNK))
  intro j _ _
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (atkinsonPhaseBlockMax_nonneg _ _ _)

def atkinsonDyadicGramBudget (N : ℕ) (W : Finset ℝ) : ℝ :=
  (Nat.clog 2 N : ℝ)*∑ j ∈ Finset.range (Nat.clog 2 N),
    (((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*atkinsonBlockCoefficientEnergy (2^j) (2^j)*
      ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax (2^j) (2^j) t u

theorem atkinsonDyadicGramBudget_nonneg (N : ℕ) (W : Finset ℝ) :
    0 ≤ atkinsonDyadicGramBudget N W := by
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (sq_nonneg _) (atkinsonBlockCoefficientEnergy_nonneg _ _))
  exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun u _ =>
    atkinsonPrefixGramMax_nonneg _ _ t u))

theorem sum_atkinsonUndampedDyadicPhaseBound_sq_le_budget (N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t N)^2 ≤ atkinsonDyadicGramBudget N W := by
  let S : ℕ → ℝ := fun j => ∑ t ∈ W, atkinsonPhaseBlockMax t (2^j) (2^j)
  let w : ℕ → ℝ := fun j => ((2^j:ℕ):ℝ)^(-(1/4:ℝ))
  have he : (∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t N) =
      ∑ j ∈ Finset.range (Nat.clog 2 N), w j*S j := by
    unfold atkinsonUndampedDyadicPhaseBound
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.mul_sum _ _ _).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (Nat.clog 2 N))
    (fun _ => (1:ℝ)) (fun j => w j*S j)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hcs
  rw [he]
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  rw [mul_pow]
  apply (mul_le_mul_of_nonneg_left (sum_atkinsonPhaseBlockMax_sq_le_gramMax (2^j) (2^j) W)
    (sq_nonneg (w j))).trans_eq
  dsimp [w]
  ring
end MathCollab.Density.Stronger.Atkinson
