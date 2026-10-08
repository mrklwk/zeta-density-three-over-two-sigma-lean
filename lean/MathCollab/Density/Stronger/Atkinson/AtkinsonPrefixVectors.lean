module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexPhase
public import MathCollab.Density.Stronger.Fourth.Coefficients
public import GuthMaynard.VanDerCorput

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Actual alternating coefficients and height-dependent prefix vectors

Each height retains its own prefix. The exact Gram entry has the minimum
of the two prefix lengths and the same zero-based source block.
-/

set_option autoImplicit false
noncomputable section

open Complex
open MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard

namespace MathCollab.Density.Stronger.Atkinson

theorem sum_range_prefix_mask {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {j N : ℕ} (hj : j ≤ N) :
    (∑ i ∈ Finset.range N, if i < j then f i else 0) = ∑ i ∈ Finset.range j, f i := by
  calc
    _ = ∑ i ∈ Finset.range j, if i < j then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i _ hi
      simp only [Finset.mem_range] at hi
      simp [hi]
    _ = _ := Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi))

def atkinsonPositivePhaseTerm (T : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-1:ℂ)^n * Complex.exp ((atkinsonSourcePhase T n : ℂ)*I)

def atkinsonPhaseBlockSum (T : ℝ) (m N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, atkinsonPositivePhaseTerm T (m+i)


def atkinsonAlternatingCoefficient (n : ℕ) : ℂ := divisorWeight n*(-1:ℂ)^n

def atkinsonPhaseVector (T : ℝ) (n : ℕ) : ℂ := unitaryPhase (atkinsonSourcePhase T n)

def atkinsonMaskedPhaseVector (T : ℝ) (m j i : ℕ) : ℂ :=
  if i < j then atkinsonPhaseVector T (m+i) else 0

def atkinsonPrefixGram (m j : ℕ) (t u : ℝ) : ℂ :=
  ∑ i ∈ Finset.range j, unitaryPhase (atkinsonSourcePhase u (m+i)-atkinsonSourcePhase t (m+i))

def atkinsonBlockCoefficientEnergy (m N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ‖divisorWeight (m+i)‖^2

theorem norm_atkinsonAlternatingCoefficient (n : ℕ) :
    ‖atkinsonAlternatingCoefficient n‖ = ‖divisorWeight n‖ := by
  simp [atkinsonAlternatingCoefficient,norm_pow]

theorem atkinsonPhaseTerm_eq_coefficient_vector (T : ℝ) (n : ℕ) :
    atkinsonPositivePhaseTerm T n = atkinsonAlternatingCoefficient n*atkinsonPhaseVector T n := by
  unfold atkinsonPositivePhaseTerm atkinsonAlternatingCoefficient atkinsonPhaseVector unitaryPhase
  rw [mul_comm I]

theorem atkinsonPhaseBlockSum_eq_masked (T : ℝ) (m : ℕ) {j N : ℕ} (hj : j ≤ N) :
    atkinsonPhaseBlockSum T m j =
      ∑ i ∈ Finset.range N, atkinsonAlternatingCoefficient (m+i)*atkinsonMaskedPhaseVector T m j i := by
  unfold atkinsonMaskedPhaseVector
  simp_rw [mul_ite,mul_zero]
  rw [sum_range_prefix_mask _ hj]
  exact Finset.sum_congr rfl (fun i _ => atkinsonPhaseTerm_eq_coefficient_vector T (m+i))

theorem atkinsonPrefixGram_eq_vector (m j : ℕ) (t u : ℝ) :
    atkinsonPrefixGram m j t u =
      ∑ i ∈ Finset.range j, conj (atkinsonPhaseVector t (m+i))*atkinsonPhaseVector u (m+i) := by
  apply Finset.sum_congr rfl
  intro i _
  unfold atkinsonPhaseVector
  rw [unitaryPhase_sub]
  ring

theorem atkinsonMaskedPhaseVector_gram (m N : ℕ) {j k : ℕ}
    (hjk : min j k ≤ N) (t u : ℝ) :
    (∑ i ∈ Finset.range N,
      conj (atkinsonMaskedPhaseVector t m j i)*atkinsonMaskedPhaseVector u m k i) =
        atkinsonPrefixGram m (min j k) t u := by
  have he (i : ℕ) :
      conj (atkinsonMaskedPhaseVector t m j i)*atkinsonMaskedPhaseVector u m k i =
        if i < min j k then conj (atkinsonPhaseVector t (m+i))*atkinsonPhaseVector u (m+i) else 0 := by
    by_cases hij : i < j <;> by_cases hik : i < k <;>
      simp [atkinsonMaskedPhaseVector,hij,hik]
  simp_rw [he]
  rw [sum_range_prefix_mask _ hjk,
    atkinsonPrefixGram_eq_vector]

theorem atkinsonPrefixGram_self (m j : ℕ) (t : ℝ) :
    atkinsonPrefixGram m j t t = (j:ℂ) := by
  simp [atkinsonPrefixGram,unitaryPhase]

theorem norm_atkinsonPrefixGram_self (m j : ℕ) (t : ℝ) :
    ‖atkinsonPrefixGram m j t t‖ = (j:ℝ) := by
  rw [atkinsonPrefixGram_self,Complex.norm_natCast]

theorem atkinsonPrefixGram_swap (m j : ℕ) (t u : ℝ) :
    atkinsonPrefixGram m j u t = conj (atkinsonPrefixGram m j t u) := by
  simp_rw [atkinsonPrefixGram_eq_vector]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul,Complex.conj_conj]
  ring

theorem atkinsonBlockCoefficientEnergy_nonneg (m N : ℕ) :
    0 ≤ atkinsonBlockCoefficientEnergy m N := by
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

end MathCollab.Density.Stronger.Atkinson
