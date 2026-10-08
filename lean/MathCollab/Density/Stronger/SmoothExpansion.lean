module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothPartition
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace MathCollab.Density.Stronger

/-- The original coefficient indexed at n+2 explicitly removes the n=1 term. -/
def smoothDyadicTerm (a : ℕ → ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  a (n+2) * (smoothDyadicWeight (((n+2 : ℕ) : ℝ)/(2 : ℝ)^j) : ℂ)

def smoothDyadicBlock (a : ℕ → ℂ) (j : ℤ) : ℂ := ∑' n : ℕ, smoothDyadicTerm a n j

theorem norm_smoothDyadicTerm (a : ℕ → ℂ) (n : ℕ) (j : ℤ) :
    ‖smoothDyadicTerm a n j‖ =
      ‖a (n+2)‖ * smoothDyadicWeight (((n+2 : ℕ) : ℝ)/(2 : ℝ)^j) := by
  rw [smoothDyadicTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (smoothDyadicWeight_bounds _).1]

theorem hasSum_norm_smoothDyadicTerm (a : ℕ → ℂ) (n : ℕ) :
    HasSum (fun j : ℤ => ‖smoothDyadicTerm a n j‖) ‖a (n+2)‖ := by
  simpa only [norm_smoothDyadicTerm, mul_one] using
    (hasSum_smoothDyadicWeight (show (0 : ℝ) < ((n+2 : ℕ) : ℝ) by positivity)).mul_left ‖a (n+2)‖

theorem hasSum_smoothDyadicTerm (a : ℕ → ℂ) (n : ℕ) :
    HasSum (fun j : ℤ => smoothDyadicTerm a n j) (a (n+2)) := by
  have hs := (hasSum_smoothDyadicWeight (show (0 : ℝ) < ((n+2 : ℕ) : ℝ) by positivity)).map
    Complex.ofRealCLM Complex.continuous_ofReal
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one,
    mul_one, smoothDyadicTerm] using hs.mul_left (a (n+2))

/-- Absolute double summability follows from the partition's exact mass one,
with no extra factor counting the number of dyadic scales. -/
theorem summable_norm_smoothDyadicTerm {a : ℕ → ℂ}
    (ha : Summable (fun n : ℕ => ‖a (n+2)‖)) :
    Summable (fun p : ℕ × ℤ => ‖smoothDyadicTerm a p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun p : ℕ × ℤ => norm_nonneg (smoothDyadicTerm a p.1 p.2))).mpr
  refine ⟨fun n => (hasSum_norm_smoothDyadicTerm a n).summable, ?_⟩
  simpa only [(hasSum_norm_smoothDyadicTerm a _).tsum_eq] using ha

theorem summable_smoothDyadicTerm {a : ℕ → ℂ}
    (ha : Summable (fun n : ℕ => ‖a (n+2)‖)) :
    Summable (fun p : ℕ × ℤ => smoothDyadicTerm a p.1 p.2) :=
  (summable_norm_smoothDyadicTerm ha).of_norm

theorem summable_smoothDyadicBlock {a : ℕ → ℂ}
    (ha : Summable (fun n : ℕ => ‖a (n+2)‖)) : Summable (smoothDyadicBlock a) :=
  (summable_smoothDyadicTerm ha).prod_symm.prod

theorem summable_norm_smoothDyadicBlock {a : ℕ → ℂ}
    (ha : Summable (fun n : ℕ => ‖a (n+2)‖)) :
    Summable (fun j : ℤ => ‖smoothDyadicBlock a j‖) := by
  have hs := summable_norm_smoothDyadicTerm ha
  apply hs.prod_symm.prod.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
  exact norm_tsum_le_tsum_norm (hs.prod_symm.prod_factor j)

/-- Exact dyadic reconstruction of the series after removing n=1. The norm
summability theorem above justifies this use of Fubini for complex series. -/
theorem tsum_smoothDyadicBlock {a : ℕ → ℂ}
    (ha : Summable (fun n : ℕ => ‖a (n+2)‖)) :
    (∑' j : ℤ, smoothDyadicBlock a j) = ∑' n : ℕ, a (n+2) := by
  unfold smoothDyadicBlock
  rw [(summable_smoothDyadicTerm ha).tsum_comm]
  exact tsum_congr (fun n => (hasSum_smoothDyadicTerm a n).tsum_eq)

theorem tsum_norm_smoothDyadicBlock_le {a : ℕ → ℂ}
    (ha : Summable (fun n : ℕ => ‖a (n+2)‖)) :
    (∑' j : ℤ, ‖smoothDyadicBlock a j‖) ≤ ∑' n : ℕ, ‖a (n+2)‖ := by
  have hs := summable_norm_smoothDyadicTerm ha
  calc
    _ ≤ ∑' j : ℤ, ∑' n : ℕ, ‖smoothDyadicTerm a n j‖ :=
      (summable_norm_smoothDyadicBlock ha).tsum_le_tsum
        (fun j => norm_tsum_le_tsum_norm (hs.prod_symm.prod_factor j)) hs.prod_symm.prod
    _ = ∑' n : ℕ, ∑' j : ℤ, ‖smoothDyadicTerm a n j‖ := hs.tsum_comm
    _ = _ := tsum_congr (fun n => (hasSum_norm_smoothDyadicTerm a n).tsum_eq)

/-- Nonpositive integer dyadic scales vanish after the n=1 term is removed. -/
theorem smoothDyadicTerm_zero_of_nonpos (a : ℕ → ℂ) (n : ℕ) {j : ℤ} (hj : j ≤ 0) :
    smoothDyadicTerm a n j = 0 := by
  have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hpow : (2 : ℝ)^j ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hj
  have hn : (2 : ℝ) ≤ ((n+2 : ℕ) : ℝ) := by norm_cast; omega
  have hratio : (3/2 : ℝ) ≤ ((n+2 : ℕ) : ℝ)/(2 : ℝ)^j :=
    (le_div_iff₀ hp).mpr (by nlinarith)
  simp only [smoothDyadicTerm, smoothDyadicWeight_zero_of_ge hratio, Complex.ofReal_zero, mul_zero]

theorem smoothDyadicBlock_zero_of_nonpos (a : ℕ → ℂ) {j : ℤ} (hj : j ≤ 0) :
    smoothDyadicBlock a j = 0 := by
  simp only [smoothDyadicBlock, smoothDyadicTerm_zero_of_nonpos a _ hj, tsum_zero]

/-- Each dyadic block is literally a finite polynomial, without imposing a
hard cutoff on the original coefficient sequence. -/
theorem smoothDyadicTerm_zero_of_large_index (a : ℕ → ℂ) (j : ℤ) {n : ℕ}
    (hn : ⌈(3/2 : ℝ)*(2 : ℝ)^j⌉₊ ≤ n) : smoothDyadicTerm a n j = 0 := by
  have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hnR : (⌈(3/2 : ℝ)*(2 : ℝ)^j⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hceil := Nat.le_ceil ((3/2 : ℝ)*(2 : ℝ)^j)
  have hratio : (3/2 : ℝ) ≤ ((n+2 : ℕ) : ℝ)/(2 : ℝ)^j := by
    apply (le_div_iff₀ hp).mpr
    push_cast
    linarith
  simp only [smoothDyadicTerm, smoothDyadicWeight_zero_of_ge hratio, Complex.ofReal_zero, mul_zero]

theorem smoothDyadicTerm_hasFiniteSupport (a : ℕ → ℂ) (j : ℤ) :
    Function.HasFiniteSupport (fun n : ℕ => smoothDyadicTerm a n j) := by
  apply Set.Finite.subset (Finset.range ⌈(3/2 : ℝ)*(2 : ℝ)^j⌉₊).finite_toSet
  intro n hn
  by_contra h
  have hn' : ⌈(3/2 : ℝ)*(2 : ℝ)^j⌉₊ ≤ n := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using h
  exact hn (smoothDyadicTerm_zero_of_large_index a j hn')

theorem smoothDyadicBlock_eq_sum_range (a : ℕ → ℂ) (j : ℤ) :
    smoothDyadicBlock a j =
      ∑ n ∈ Finset.range ⌈(3/2 : ℝ)*(2 : ℝ)^j⌉₊, smoothDyadicTerm a n j := by
  apply tsum_eq_sum
  intro n hn
  exact smoothDyadicTerm_zero_of_large_index a j (by simpa only [Finset.mem_range, not_lt] using hn)

/-- Truncating large dyadic scales costs at most the original absolute tail
starting at R/2. Each retained weight remains smooth in its argument. -/
theorem smoothDyadicBlock_scale_tail_le {a : ℕ → ℂ}
    (ha : Summable (fun n : ℕ => ‖a (n+2)‖)) (R : ℝ) :
    (∑' j : ℤ, if R < (2 : ℝ)^j then ‖smoothDyadicBlock a j‖ else 0) ≤
      ∑' n : ℕ, if R/2 < ((n+2 : ℕ) : ℝ) then ‖a (n+2)‖ else 0 := by
  let F : ℕ → ℤ → ℝ := fun n j =>
    if R < (2 : ℝ)^j then ‖smoothDyadicTerm a n j‖ else 0
  have hFnonneg (n : ℕ) (j : ℤ) : 0 ≤ F n j := by dsimp [F]; split_ifs <;> positivity
  have hFle (n : ℕ) (j : ℤ) : F n j ≤ ‖smoothDyadicTerm a n j‖ := by
    dsimp [F]; split_ifs <;> simp
  have hs := summable_norm_smoothDyadicTerm ha
  have hF : Summable (Function.uncurry F) :=
    hs.of_nonneg_of_le (fun p => hFnonneg p.1 p.2) (fun p => hFle p.1 p.2)
  have hrow (n : ℕ) : (∑' j : ℤ, F n j) ≤
      if R/2 < ((n+2 : ℕ) : ℝ) then ‖a (n+2)‖ else 0 := by
    by_cases hn : R/2 < ((n+2 : ℕ) : ℝ)
    · rw [ite_eq_left hn]
      exact ((hF.prod_factor n).tsum_le_tsum (hFle n) (hs.prod_factor n)).trans_eq
        (hasSum_norm_smoothDyadicTerm a n).tsum_eq
    · rw [ite_eq_right hn]
      have hz (j : ℤ) : F n j = 0 := by
        dsimp [F]
        split_ifs with hj
        · have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
          have hr : ((n+2 : ℕ) : ℝ)/(2 : ℝ)^j ≤ 5/8 :=
            (div_le_iff₀ hp).mpr (by nlinarith)
          simp only [smoothDyadicTerm, smoothDyadicWeight_zero_of_le hr,
            Complex.ofReal_zero, mul_zero, norm_zero]
        · rfl
      simp only [hz, tsum_zero, le_refl]
  have hcol (j : ℤ) : (if R < (2 : ℝ)^j then ‖smoothDyadicBlock a j‖ else 0) ≤
      ∑' n : ℕ, F n j := by
    by_cases hj : R < (2 : ℝ)^j
    · simpa only [F, ite_eq_left hj, smoothDyadicBlock, Prod.swap] using
        norm_tsum_le_tsum_norm (hs.prod_symm.prod_factor j)
    · simp only [F, ite_eq_right hj, tsum_zero, le_refl]
  have hleft : Summable (fun j : ℤ => if R < (2 : ℝ)^j then ‖smoothDyadicBlock a j‖ else 0) :=
    (summable_norm_smoothDyadicBlock ha).of_nonneg_of_le
      (fun j => by split_ifs <;> positivity) (fun j => by split_ifs <;> simp)
  have hright : Summable (fun n : ℕ => if R/2 < ((n+2 : ℕ) : ℝ) then ‖a (n+2)‖ else 0) :=
    ha.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> simp)
  calc
    _ ≤ ∑' j : ℤ, ∑' n : ℕ, F n j := hleft.tsum_le_tsum hcol hF.prod_symm.prod
    _ = ∑' n : ℕ, ∑' j : ℤ, F n j := hF.tsum_comm
    _ ≤ _ := hF.prod.tsum_le_tsum hrow hright

end MathCollab.Density.Stronger
