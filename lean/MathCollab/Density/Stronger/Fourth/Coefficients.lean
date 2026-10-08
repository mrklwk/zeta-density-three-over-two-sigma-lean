module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.DivisorGrowth
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

noncomputable def divisorWeight (n : ℕ) : ℂ :=
  (n.divisors.card : ℂ)
noncomputable def afeCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
/-- One term of the ordinary divisor Dirichlet series. -/
noncomputable def divisorDirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun k : ℕ => (k.divisors.card : ℂ)) s n

/-- On positive indices the opened divisor series is literally the DFI
divisor coefficient times the corresponding complex power. -/
theorem divisorDirichletTerm_eq_divisorWeight_mul_cpow
    (s : ℂ) (n : ℕ) :
    divisorDirichletTerm s n =
      divisorWeight n * (n : ℂ) ^ (-s) := by
  unfold divisorDirichletTerm divisorWeight
  rw [LSeries.term_def₀]
  simp


theorem norm_fourth_divisorTerm_vertical (t c u : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖ =
      (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c)) := by
  by_cases hn : n = 0
  · subst n
    simp [divisorDirichletTerm]
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [divisorDirichletTerm_eq_divisorWeight_mul_cpow, norm_mul]
  simp only [divisorWeight,Complex.norm_natCast]
  rw [show (n:ℂ) = ((n:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  congr 2
  norm_num [afeCriticalPoint]


def zetaFourthCoeff (c : ℝ) (n : ℕ) : ℂ :=
  divisorDirichletTerm ((1/2+c:ℝ):ℂ) n

theorem zetaFourthCoeff_zero (c : ℝ) : zetaFourthCoeff c 0 = 0 := by
  simp [zetaFourthCoeff,divisorDirichletTerm]

theorem zetaFourthCoeff_one (c : ℝ) : zetaFourthCoeff c 1 = 1 := by
  simp [zetaFourthCoeff,divisorDirichletTerm_eq_divisorWeight_mul_cpow,divisorWeight]

theorem norm_zetaFourthCoeff (c : ℝ) (n : ℕ) :
    ‖zetaFourthCoeff c n‖ = (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c)) := by
  simpa [zetaFourthCoeff,afeCriticalPoint] using norm_fourth_divisorTerm_vertical 0 c 0 n


theorem exists_norm_sq_zetaFourthCoeff_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ n : ℕ, 0 < n →
      ‖zetaFourthCoeff c n‖^2 ≤ D*(n:ℝ)^(ε-1) := by
  obtain ⟨C,hC₁,hdiv⟩ := MathCollab.Density.divisor_card_subpower (show 0 < ε/2 by positivity)
  have hC : 0 < C := zero_lt_one.trans_le hC₁
  refine ⟨C^2,pow_pos hC 2,?_⟩
  intro c hc n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hbase : ‖zetaFourthCoeff c n‖ ≤ C*(n:ℝ)^(ε/2-(1/2+c)) := by
    rw [norm_zetaFourthCoeff]
    calc
      _ ≤ (C*(n:ℝ)^(ε/2))*(n:ℝ)^(-(1/2+c)) :=
        mul_le_mul_of_nonneg_right (hdiv n hn) (by positivity)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hn0]; rfl
  calc
    _ ≤ (C*(n:ℝ)^(ε/2-(1/2+c)))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbase 2
    _ = C^2*(n:ℝ)^(ε-1-2*c) := by
      rw [mul_pow,← Real.rpow_mul_natCast hn0.le]
      congr 2
      norm_num
      ring
    _ ≤ C^2*(n:ℝ)^(ε-1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (sq_nonneg C)

theorem sum_rpow_sub_one_dyadic_le {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N (2*N), (n:ℝ)^(ε-1)) ≤ (2*(N:ℝ))^ε := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hpoint : ∀ n ∈ Finset.Ioc N (2*N),
      (n:ℝ)^(ε-1) ≤ (2*(N:ℝ))^ε/(N:ℝ) := by
    intro n hn
    have hnN : (N:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
    have hn2N : (n:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hn0 : (0:ℝ) < n := hN0.trans_le hnN
    rw [Real.rpow_sub_one hn0.ne']
    exact div_le_div₀ (by positivity) (Real.rpow_le_rpow hn0.le hn2N hε) hN0 hnN
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc N (2*N), (2*(N:ℝ))^ε/(N:ℝ) :=
      Finset.sum_le_sum hpoint
    _ = _ := by
      simp only [Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul]
      have heq : 2*N-N = N := by omega
      rw [heq]
      field_simp

theorem exists_sum_sq_zetaFourthCoeff_dyadic_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ c : ℝ, 0 ≤ c → ∀ N : ℕ, 0 < N →
      (∑ n ∈ Finset.Ioc N (2*N), ‖zetaFourthCoeff c n‖^2) ≤
        D*(2*(N:ℝ))^ε := by
  obtain ⟨D,hD,hpoint⟩ := exists_norm_sq_zetaFourthCoeff_le hε
  have hD1 : 1 ≤ D := by simpa [zetaFourthCoeff_one] using hpoint 0 le_rfl 1 (by decide)
  refine ⟨D,hD1,?_⟩
  intro c hc N hN
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N (2*N), D*(n:ℝ)^(ε-1) :=
      Finset.sum_le_sum (fun n hn => hpoint c hc n
        (hN.trans (Finset.mem_Ioc.mp hn).1))
    _ = D*(∑ n ∈ Finset.Ioc N (2*N), (n:ℝ)^(ε-1)) := (Finset.mul_sum ..).symm
    _ ≤ D*(2*(N:ℝ))^ε :=
      mul_le_mul_of_nonneg_left (sum_rpow_sub_one_dyadic_le hε.le hN) hD.le

end MathCollab.Density.Stronger.Fourth
