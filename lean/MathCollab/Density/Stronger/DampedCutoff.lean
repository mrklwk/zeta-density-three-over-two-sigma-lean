module
-- Reversible module-visibility port of the audited development.
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Set
open scoped BigOperators ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Smooth exponential damping, with the dimensionless parameter q=N/Y. -/
def dampedCutoff (ψ : ℝ → ℝ) (q y : ℝ) : ℝ := ψ y * Real.exp (-q * y)

theorem dampedCutoff_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (q : ℝ) :
    ContDiff ℝ ∞ (dampedCutoff ψ q) := by
  unfold dampedCutoff
  exact hψ.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

theorem dampedCutoff_tsupport (ψ : ℝ → ℝ) (q : ℝ) :
    tsupport (dampedCutoff ψ q) ⊆ tsupport ψ := tsupport_mul_subset_left

/-- Explicit domination of every parameter power by the damping. -/
theorem damping_power_bound {a q y : ℝ} (ha : 0 < a) (hq : 0 ≤ q)
    (hy : a ≤ y) (n : ℕ) :
    q^n * Real.exp (-q*y) ≤ (n.factorial : ℝ) / a^n := by
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hp : (q*a)^n ≤ (n.factorial : ℝ) * Real.exp (q*a) := by
    have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (q*a) (mul_nonneg hq ha.le) n)
    simpa only [mul_comm] using h
  have he : Real.exp (-q*y) ≤ Real.exp (-(q*a)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  apply (le_div_iff₀ (pow_pos ha n)).2
  calc
    q^n * Real.exp (-q*y) * a^n = (q*a)^n * Real.exp (-q*y) := by
      rw [mul_pow]
      ring
    _ ≤ ((n.factorial : ℝ) * Real.exp (q*a)) * Real.exp (-(q*a)) := by
      exact mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = n.factorial := by rw [mul_assoc, ← Real.exp_add]; simp

theorem norm_iteratedDeriv_damping_le {a q y : ℝ}
    (ha : 0 < a) (hq : 0 ≤ q) (hy : a ≤ y) (n : ℕ) :
    ‖iteratedDeriv n (fun x : ℝ => Real.exp (-q*x)) y‖ ≤
      (n.factorial : ℝ) / a^n := by
  rw [iteratedDeriv_exp_const_mul, norm_mul, norm_pow,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg hq, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact damping_power_bound ha hq hy n

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]; exact Subset.rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- The constant precedes the unbounded damping parameter and the argument.
This supplies the uniform smoothness input; no Mellin decay is assumed here. -/
theorem dampedCutoff_uniform_derivatives {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hs : tsupport ψ ⊆ Icc a b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 0 ≤ q → ∀ y : ℝ,
      ‖iteratedDeriv n (dampedCutoff ψ q) y‖ ≤ C := by
  have hb (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc a b, ‖iteratedDeriv i ψ y‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image
      ((hψ.continuous_iteratedDeriv i (by simp)).norm.continuousOn)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro y hy
    exact (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  choose B hBpos hB using hb
  let C : ℝ := ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ) * B i * ((n-i).factorial : ℝ) / a^(n-i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => by
    have := hBpos i
    positivity)
  refine ⟨C, hC, ?_⟩
  intro q hq y
  by_cases hy : y ∈ Icc a b
  · have he : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (-q*x)) := by fun_prop
    have hd : iteratedDeriv n (dampedCutoff ψ q) y =
        ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * iteratedDeriv i ψ y *
          iteratedDeriv (n-i) (fun x : ℝ => Real.exp (-q*x)) y := by
      exact iteratedDeriv_fun_mul (hψ.of_le (by simp)).contDiffAt
        (he.of_le (by simp)).contDiffAt
    rw [hd]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    have hBi := hBpos i
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ ((n.choose i : ℝ) * B i) * ((n-i).factorial / a^(n-i)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hB i y hy) (Nat.cast_nonneg _))
          (norm_iteratedDeriv_damping_le ha hq hy.1 (n-i)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hn : y ∉ tsupport (iteratedDeriv n (dampedCutoff ψ q)) := by
      intro h
      exact hy (hs ((dampedCutoff_tsupport ψ q) ((tsupport_iteratedDeriv_subset _ n) h)))
    rw [image_eq_zero_of_notMem_tsupport hn, norm_zero]
    exact hC

end MathCollab.Density.Stronger
