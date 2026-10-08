module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Fourth.MeanValueCore
public import MathCollab.Density.Stronger.Fourth.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

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


theorem dirichletTime_shift (N : ℕ) (a : ℕ → ℂ) (v t : ℝ) :
    dirichletTime N a (t+v) = dirichletTime N (endpointTwist v a) t := by
  unfold dirichletTime
  apply Finset.sum_congr rfl
  intro n _
  rw [endpointTwist,mul_assoc (a n),← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem integral_norm_sq_dirichletTime_interval_le
    (N : ℕ) (a : ℕ → ℂ) {A B : ℝ} (hN : 0 < N) (hAB : A ≤ B) :
    (∫ t : ℝ in A..B, ‖dirichletTime N a t‖^2) ≤
      (B-A+2*(5*Real.pi+1)*(N:ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  have h := integral_norm_sq_dirichletTime_le N (B-A) (endpointTwist A a)
    hN (sub_nonneg.mpr hAB)
  have heq :
      (∫ t : ℝ in A..B, ‖dirichletTime N a t‖^2) =
        ∫ t : ℝ in 0..B-A, ‖dirichletTime N (endpointTwist A a) t‖^2 := by
    have ht := intervalIntegral.integral_comp_add_right
      (fun t : ℝ => ‖dirichletTime N a t‖^2) A (a := 0) (b := B-A)
    simpa only [dirichletTime_shift,zero_add,sub_add_cancel] using ht.symm
  rw [heq]
  simpa only [norm_endpointTwist] using h

theorem integral_norm_sq_dirichletTime_reflected_le
    (N : ℕ) (a : ℕ → ℂ) (u : ℝ) {H : ℝ} (hN : 0 < N) (hH : 0 ≤ H) :
    (∫ t : ℝ in H..2*H, ‖dirichletTime N a (u-t)‖^2) ≤
      (H+2*(5*Real.pi+1)*(N:ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => ‖dirichletTime N a t‖^2) u]
  have h := integral_norm_sq_dirichletTime_interval_le N a hN
    (show u-2*H ≤ u-H by linarith)
  have heq : u-H-(u-2*H) = H := by ring
  simpa only [heq] using h


def dirichletPrefix (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, a n*Complex.exp (-(I*(t:ℂ)*(Real.log n:ℂ)))

theorem continuous_dirichletPrefix (N : ℕ) (a : ℕ → ℂ) :
    Continuous (dirichletPrefix N a) := by
  unfold dirichletPrefix
  fun_prop

theorem dirichletPrefix_one (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix 1 a t = a 1 := by
  simp [dirichletPrefix]

theorem dirichletPrefix_double (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix (2*N) a t = dirichletPrefix N a t+dirichletTime N a t := by
  exact (Finset.sum_Ioc_consecutive
    (fun n : ℕ => a n*Complex.exp (-(I*(t:ℂ)*(Real.log n:ℂ))))
    (Nat.zero_le N) (by omega : N ≤ 2*N)).symm

theorem dirichletPrefix_pow_two (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix (2^M) a t =
      a 1+∑ j ∈ Finset.range M, dirichletTime (2^j) a t := by
  induction M with
  | zero => simp [dirichletPrefix_one]
  | succ M ih =>
    rw [pow_succ, Nat.mul_comm (2^M) 2,dirichletPrefix_double,ih,
      Finset.sum_range_succ,add_assoc]

theorem norm_dirichletPrefix_pow_two_sq_le (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPrefix (2^M) a t‖^2 ≤
      2*((M:ℝ)+1)*(‖a 1‖^2+∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) := by
  let S : ℂ := ∑ j ∈ Finset.range M, dirichletTime (2^j) a t
  let Q : ℝ := ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : ‖S‖^2 ≤ (M:ℝ)*Q := by
    simpa [S,Q] using norm_sum_mul_sq_le (Finset.range M)
      (fun _ => (1:ℂ)) (fun j => dirichletTime (2^j) a t)
  rw [dirichletPrefix_pow_two]
  change ‖a 1+S‖^2 ≤ 2*((M:ℝ)+1)*(‖a 1‖^2+Q)
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a 1) S) 2
  have hM : 0 ≤ (M:ℝ) := Nat.cast_nonneg M
  nlinarith [sq_nonneg (‖a 1‖-‖S‖),mul_nonneg hM (sq_nonneg ‖a 1‖)]


theorem integral_norm_sq_dirichletPrefix_le_blocks
    (M : ℕ) (a : ℕ → ℂ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)*((B-A)*‖a 1‖^2+
        ∑ j ∈ Finset.range M, ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) := by
  have hi (j : ℕ) : IntervalIntegrable
      (fun t : ℝ => ‖dirichletTime (2^j) a t‖^2) volume A B :=
    ((continuous_dirichletTime (2^j) a).norm.pow 2).intervalIntegrable A B
  have hsum : IntervalIntegrable
      (fun t : ℝ => ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) volume A B := by
    convert IntervalIntegrable.sum (Finset.range M) (fun j _ => hi j) using 1
    ext t
    simp
  have hconst : IntervalIntegrable (fun _ : ℝ => ‖a 1‖^2) volume A B :=
    intervalIntegrable_const
  calc
    _ ≤ ∫ t : ℝ in A..B,
        2*((M:ℝ)+1)*(‖a 1‖^2+
          ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) :=
      intervalIntegral.integral_mono_on hAB
        (((continuous_dirichletPrefix (2^M) a).norm.pow 2).intervalIntegrable A B)
        ((hconst.add hsum).const_mul _)
        (fun t _ => norm_dirichletPrefix_pow_two_sq_le M a t)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hconst hsum,
        intervalIntegral.integral_const,
        intervalIntegral.integral_finsetSum (fun j _ => hi j)]
      rfl

theorem integral_norm_sq_dirichletPrefix_le
    (M : ℕ) (a : ℕ → ℂ) {A B L : ℝ} (hAB : A ≤ B)
    (hone : ‖a 1‖^2 ≤ L)
    (hcoeff : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖a n‖^2) ≤ L) :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)^2*(B-A+2*(5*Real.pi+1)*(2:ℝ)^M)*L := by
  have hL : 0 ≤ L := (sq_nonneg ‖a 1‖).trans hone
  have hT : 0 ≤ B-A := sub_nonneg.mpr hAB
  let E : ℝ := (B-A+2*(5*Real.pi+1)*(2:ℝ)^M)*L
  have hfirst : (B-A)*‖a 1‖^2 ≤ E := by
    dsimp [E]
    apply mul_le_mul (le_add_of_nonneg_right (by positivity)) hone (sq_nonneg _)
    positivity
  have hblock : ∀ j ∈ Finset.range M,
      (∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) ≤ E := by
    intro j hj
    have hjM : j ≤ M := (Finset.mem_range.mp hj).le
    have hp : ((2^j:ℕ):ℝ) ≤ (2:ℝ)^M := by
      norm_cast
      exact pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) hjM
    apply (integral_norm_sq_dirichletTime_interval_le (2^j) a
      (by positivity) hAB).trans
    dsimp [E]
    apply mul_le_mul (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hp (by positivity)))
      (hcoeff j hj) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    positivity
  have hsum : (∑ j ∈ Finset.range M,
      ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) ≤ (M:ℝ)*E := by
    simpa using Finset.sum_le_sum hblock
  calc
    _ ≤ 2*((M:ℝ)+1)*((B-A)*‖a 1‖^2+
        ∑ j ∈ Finset.range M, ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) :=
      integral_norm_sq_dirichletPrefix_le_blocks M a hAB
    _ ≤ 2*((M:ℝ)+1)*((M:ℝ)+1)*E := by
      rw [mul_assoc (2*((M:ℝ)+1))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = _ := by dsimp [E]; ring

theorem integral_norm_sq_dirichletPrefix_reflected_le
    (M : ℕ) (a : ℕ → ℂ) (u : ℝ) {H L : ℝ} (hH : 0 ≤ H)
    (hone : ‖a 1‖^2 ≤ L)
    (hcoeff : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖a n‖^2) ≤ L) :
    (∫ t : ℝ in H..2*H, ‖dirichletPrefix (2^M) a (u-t)‖^2) ≤
      2*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*L := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => ‖dirichletPrefix (2^M) a t‖^2) u]
  have h := integral_norm_sq_dirichletPrefix_le M a
    (show u-2*H ≤ u-H by linarith) hone hcoeff
  have heq : u-H-(u-2*H) = H := by ring
  simpa only [heq] using h


theorem fourth_divisorTerm_eq_coeff_phase (t c u : ℝ) (n : ℕ) :
    divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n =
      zetaFourthCoeff c n*Complex.exp (-(I*((u-t):ℂ)*(Real.log n:ℂ))) := by
  by_cases hn : n = 0
  · subst n
    simp [divisorDirichletTerm,zetaFourthCoeff_zero]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  rw [zetaFourthCoeff,divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    Complex.cpow_def_of_ne_zero hnC,Complex.cpow_def_of_ne_zero hnC,
    mul_assoc (divisorWeight n),← Complex.exp_add]
  congr 1
  congr 1
  rw [← Complex.natCast_log]
  dsimp [afeCriticalPoint]
  push_cast
  ring

theorem sum_fourth_divisorTerm_eq_prefix (t c u : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N+1),
      divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n) =
        dirichletPrefix N (zetaFourthCoeff c) (u-t) := by
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N,
        divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        simp only [Finset.mem_Ioc,Finset.mem_range] at *
        omega
      · intro n hn hnot
        have hn0 : n = 0 := by
          simp only [Finset.mem_Ioc,Finset.mem_range] at *
          omega
        subst n
        simp [divisorDirichletTerm]
    _ = _ := by
      simp only [fourth_divisorTerm_eq_coeff_phase,dirichletPrefix,Complex.ofReal_sub]


theorem norm_dirichletPrefix_le (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPrefix N a t‖ ≤ ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ := by
  unfold dirichletPrefix
  apply norm_sum_le_of_le
  intro n _
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.neg_re,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,one_mul,zero_add,sub_zero,
    neg_zero,Real.exp_zero,mul_one]
  exact le_rfl

theorem continuous_dirichletPrefix_reflected (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    Continuous (fun u : ℝ => dirichletPrefix N a (u-t)) :=
  (continuous_dirichletPrefix N a).comp (by fun_prop)

theorem integrable_gaussian_dirichletPrefix_norm_pow
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (t : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ => Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^k) := by
  let C : ℝ := ∑ n ∈ Finset.Ioc 0 N, ‖a n‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcont : Continuous (fun u : ℝ =>
      Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^k) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-b*u^2))).mul
      ((continuous_dirichletPrefix_reflected N a t).norm.pow k)
  apply ((integrable_exp_neg_mul_sq hb).mul_const (C^k)).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletPrefix_le N a (u-t)) k)
    (Real.exp_pos _).le

end MathCollab.Density.Stronger.Fourth
