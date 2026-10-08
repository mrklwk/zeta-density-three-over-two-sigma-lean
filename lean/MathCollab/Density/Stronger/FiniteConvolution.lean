module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.DetectorPoweredPieces
public import MathCollab.Density.Stronger.BoundedConvolution

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Literal product support for every finite block, including smooth weights. -/
theorem finiteBlock_pow_support {f : ArithmeticFunction ℂ} {N : ℕ}
    (hs : ∀ n, f n ≠ 0 → n ∈ Finset.Ioc N (2*N)) (k n : ℕ)
    (hn : (f^k) n ≠ 0) : 0 < n ∧ n ≤ (2*N)^k := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply] at hn
    split_ifs at hn with he
    · subst n; simp
    · exact False.elim (hn rfl)
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hi := ih p.1 (left_ne_zero_of_mul hmul)
    have hb := hs p.2 (right_ne_zero_of_mul hmul)
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    refine ⟨Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp hp).2, ?_⟩
    rw [← he, pow_succ]
    exact Nat.mul_le_mul hi.2 (Finset.mem_Ioc.mp hb).2

theorem finiteBlock_pow_lower {f : ArithmeticFunction ℂ} {N : ℕ} (hN : 0 < N)
    (hs : ∀ n, f n ≠ 0 → n ∈ Finset.Ioc N (2*N))
    (k n : ℕ) (hn : (f^(k+1)) n ≠ 0) : N^(k+1) < n := by
  induction k generalizing n with
  | zero =>
    simp only [zero_add, pow_one] at hn ⊢
    exact (Finset.mem_Ioc.mp (hs n hn)).1
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have ha := ih p.1 (left_ne_zero_of_mul hmul)
    have hb := hs p.2 (right_ne_zero_of_mul hmul)
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, pow_succ]
    exact Nat.mul_lt_mul_of_pos_right ha hN |>.trans_le
      (Nat.mul_le_mul_left _ (Finset.mem_Ioc.mp hb).1.le)

theorem finiteBlock_pow_LSeriesSummable {f : ArithmeticFunction ℂ} {N : ℕ}
    (hs : ∀ n, f n ≠ 0 → n ∈ Finset.Ioc N (2*N)) (k : ℕ) (s : ℂ) :
    LSeriesSummable (fun n => (f^k) n) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.range ((2*N)^k+1)).finite_toSet
  intro n hn
  apply Finset.mem_range.mpr
  by_contra h
  have hz : (f^k) n = 0 := by
    by_contra hh
    have hi := finiteBlock_pow_support hs k n hh
    omega
  have ht : LSeries.term (fun n => (f^k) n) s n = 0 := by
    rw [LSeries.term_def₀ (f^k).map_zero]
    simp [hz]
  exact hn ht

/-- The finite Dirichlet convolution has exactly the original power as its L-series. -/
theorem finiteBlock_LSeries_pow {f : ArithmeticFunction ℂ} {N : ℕ}
    (hs : ∀ n, f n ≠ 0 → n ∈ Finset.Ioc N (2*N)) (k : ℕ) (s : ℂ) :
    LSeries (fun n => (f^k) n) s = (LSeries f s)^k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    rw [LSeries, tsum_eq_single 1]
    · simp [ArithmeticFunction.one_apply]
    · intro n hn
      simp [LSeries.term_def, ArithmeticFunction.one_apply, hn]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.LSeries_mul'
      (finiteBlock_pow_LSeriesSummable hs k s)
      (by simpa using finiteBlock_pow_LSeriesSummable hs 1 s), ih, pow_succ]

theorem finiteBlock_pow_LSeries_sum {f : ArithmeticFunction ℂ} {N k : ℕ}
    (hN : 0 < N) (hk : 0 < k)
    (hs : ∀ n, f n ≠ 0 → n ∈ Finset.Ioc N (2*N)) (s : ℂ) :
    LSeries (fun n => (f^k) n) s =
      ∑ n ∈ Finset.Ioc (N^k) ((2*N)^k), (f^k) n*(n : ℂ)^(-s) := by
  rw [LSeries, tsum_eq_sum (s := Finset.Ioc (N^k) ((2*N)^k))]
  · apply Finset.sum_congr rfl
    intro n _
    rw [LSeries.term_def₀ (f^k).map_zero]
  · intro n hn
    rw [LSeries.term_def₀ (f^k).map_zero]
    have hz : (f^k) n = 0 := by
      by_contra hh
      have hu := (finiteBlock_pow_support hs k n hh).2
      have hl : N^k < n := by
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
        exact finiteBlock_pow_lower hN hs l n hh
      exact hn (Finset.mem_Ioc.mpr ⟨hl, hu⟩)
    rw [hz, zero_mul]

/-- One of k fixed pieces detects the powered block at the same ordinate,
with exactly the factor k. Coefficients are conjugated for the positive phase. -/
theorem exists_finiteBlock_powered_piece {f : ArithmeticFunction ℂ} {N k : ℕ}
    (hN : 0 < N) (hk : 0 < k)
    (hs : ∀ n, f n ≠ 0 → n ∈ Finset.Ioc N (2*N)) (t : ℝ) :
    ∃ ℓ ∈ Finset.range k, ‖LSeries f (Complex.I*(t : ℂ))‖^k/(k : ℝ) ≤
      ‖detectingPolynomial (2^ℓ*N^k) (fun n => conj ((f^k) n)) t‖ := by
  let g := fun n : ℕ => (f^k) n*(n : ℂ)^(-(Complex.I*(t : ℂ)))
  have he : ‖LSeries f (Complex.I*(t : ℂ))‖^k =
      ‖∑ ℓ ∈ Finset.range k, ∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), g n‖ := by
    rw [← norm_pow, ← finiteBlock_LSeries_pow hs,
      finiteBlock_pow_LSeries_sum hN hk hs, sum_scaled_dyadic_Ioc, mul_pow]
  have hn (ℓ : ℕ) :
      ‖detectingPolynomial (2^ℓ*N^k) (fun n => conj ((f^k) n)) t‖ =
      ‖∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), g n‖ := by
    rw [norm_detectingPolynomial_conj,
      norm_detectingPolynomial_eq_cpow_sum (by positivity)]
  by_contra h
  push Not at h
  have hslt : (∑ ℓ ∈ Finset.range k,
      ‖∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), g n‖) <
      ‖LSeries f (Complex.I*(t : ℂ))‖^k := by
    calc
      _ < ∑ _ℓ ∈ Finset.range k, ‖LSeries f (Complex.I*(t : ℂ))‖^k/(k : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hk⟩
        intro ℓ hℓ
        rw [← hn]
        exact h ℓ hℓ
      _ = _ := by simp; field_simp
  have hb := norm_sum_le (Finset.range k)
    (fun ℓ => ∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), g n)
  rw [← he] at hb
  linarith

end MathCollab.Density.Stronger
