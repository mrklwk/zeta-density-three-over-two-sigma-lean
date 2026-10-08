module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixVectors

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

noncomputable def phaseAlign (z : ℂ) : ℂ := if z = 0 then 1 else conj z / ‖z‖

theorem norm_conj_eq (z : ℂ) : ‖conj z‖ = ‖z‖ := by
  change ‖star z‖ = ‖z‖
  exact norm_star z

theorem norm_phaseAlign_le_one (z : ℂ) : ‖phaseAlign z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · rw [phaseAlign, ite_eq_right hz, norm_div]
    rw [norm_conj_eq, norm_real]
    have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [hzNorm]

theorem phaseAlign_mul (z : ℂ) : phaseAlign z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · rw [phaseAlign, ite_eq_right hz]
    calc
      conj z / ‖z‖ * z = (conj z * z) / ‖z‖ := by ring
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / ‖z‖ := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      _ = (‖z‖ : ℂ) := by
        push_cast
        have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        field_simp

/-- Coordinate Cauchy--Schwarz for a finite complex sum. -/
theorem norm_sum_mul_sq_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) := by
  calc
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => by rw [norm_mul])
    _ ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) :=
      sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)

/-- The finite Gram-matrix bound underlying Halász--Montgomery duality. -/
theorem sum_norm_sq_sum_le_gram {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (c : κ → ℂ) (y : κ → ι → ℂ)
    (hc : ∀ t ∈ W, ‖c t‖ ≤ 1) :
    (∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (y t n) * y u n‖ := by
  have hexpand :
      ((∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
        ∑ t ∈ W, ∑ u ∈ W,
          conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n) := by
    have hpoint (n : ι) :
        ((‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
          conj (∑ t ∈ W, c t * y t n) * (∑ t ∈ W, c t * y t n) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    have hcast :
        ((∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
          ∑ n ∈ s, ((‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast]
    simp_rw [hpoint]
    simp only [map_sum, map_mul]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hre := congrArg Complex.re hexpand
  simp only [ofReal_re] at hre
  rw [hre]
  calc
    Complex.re (∑ t ∈ W, ∑ u ∈ W,
        conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)) ≤
        ‖∑ t ∈ W, ∑ u ∈ W,
          conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => norm_sum_le _ _)
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖∑ n ∈ s, conj (y t n) * y u n‖ := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, norm_mul]
      rw [norm_conj_eq]
      have hct := hc t ht
      have hcu := hc u hu
      have hprod : ‖c t‖ * ‖c u‖ ≤ 1 := by
        calc
          ‖c t‖ * ‖c u‖ ≤ 1 * 1 :=
            mul_le_mul hct hcu (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      exact (mul_le_mul_of_nonneg_right hprod
        (norm_nonneg (∑ n ∈ s, conj (y t n) * y u n))).trans_eq (one_mul _)


theorem sum_norm_coefficient_vector_sq_le_gram
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (d : ι → ℂ) (e : κ → ι → ℂ) :
    (∑ t ∈ W, ‖∑ n ∈ s, d n*e t n‖)^2 ≤
      (∑ n ∈ s, ‖d n‖^2)*
        ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (e t n)*e u n‖ := by
  let D : κ → ℂ := fun t => ∑ n ∈ s, d n*e t n
  let c : κ → ℂ := fun t => phaseAlign (D t)
  have hc : ∀ t ∈ W, ‖c t‖ ≤ 1 := fun t _ => norm_phaseAlign_le_one (D t)
  have halign : ‖∑ t ∈ W, c t*D t‖ = ∑ t ∈ W, ‖D t‖ := by
    have he : (∑ t ∈ W, c t*D t) = ((∑ t ∈ W, ‖D t‖ : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl (fun t _ => phaseAlign_mul (D t))
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hexpand : (∑ t ∈ W, c t*D t) =
      ∑ n ∈ s, d n*(∑ t ∈ W, c t*e t n) := by
    simp only [D,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hcs := norm_sum_mul_sq_le s d (fun n => ∑ t ∈ W, c t*e t n)
  rw [← hexpand,halign] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (sum_norm_sq_sum_le_gram s W c e hc) (by positivity))

theorem card_mul_lower_sq_le_coefficient_gram
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (d : ι → ℂ) (e : κ → ι → ℂ)
    {V : ℝ} (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ W, V ≤ ‖∑ n ∈ s, d n*e t n‖) :
    ((W.card:ℝ)*V)^2 ≤ (∑ n ∈ s, ‖d n‖^2)*
      ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (e t n)*e u n‖ := by
  have hsum : (W.card:ℝ)*V ≤ ∑ t ∈ W, ‖∑ n ∈ s, d n*e t n‖ := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hlarge
  exact (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hV) hsum 2).trans
    (sum_norm_coefficient_vector_sq_le_gram s W d e)


end MathCollab.Density.Stronger.Atkinson
