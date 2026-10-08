module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Fourth.PrefixMean
public import MathCollab.Density.Stronger.CriticalMoment
public import MathCollab.Density.Stronger.DyadicMoment
public import Mathlib.MeasureTheory.Integral.Prod

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem exists_integral_sq_fourthPolynomial_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ,
      ∀ H : ℝ, 0 ≤ H → ∀ u : ℝ,
      (∫ t : ℝ in H..2*H,
        ‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε := by
  obtain ⟨C,hC,hcoeff⟩ := exists_sum_sq_zetaFourthCoeff_dyadic_le hε
  refine ⟨2*C,by linarith,?_⟩
  intro c hc M H hH u
  let L : ℝ := C*((2:ℝ)^M)^ε
  have hpow : 1 ≤ ((2:ℝ)^M)^ε :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hε.le
  have hone : ‖zetaFourthCoeff c 1‖^2 ≤ L := by
    simp only [zetaFourthCoeff_one,norm_one,one_pow]
    dsimp [L]
    nlinarith
  have hmass : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖zetaFourthCoeff c n‖^2) ≤ L := by
    intro j hj
    have hjM : j+1 ≤ M := Finset.mem_range.mp hj
    have hsize : 2*((2^j:ℕ):ℝ) ≤ (2:ℝ)^M := by
      norm_cast
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) hjM
    apply (hcoeff c hc (2^j) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hsize hε.le) (by linarith)
  calc
    _ ≤ 2*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*L :=
      integral_norm_sq_dirichletPrefix_reflected_le M (zetaFourthCoeff c) u hH hone hmass
    _ = _ := by dsimp [L]; ring

theorem exists_integral_sq_fourthDivisorSum_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ,
      ∀ H : ℝ, 0 ≤ H → ∀ u : ℝ,
      (∫ t : ℝ in H..2*H,
        ‖∑ n ∈ Finset.range (2^M+1),
          divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε := by
  simpa only [sum_fourth_divisorTerm_eq_prefix] using
    exists_integral_sq_fourthPolynomial_le hε


theorem integrable_gaussian_dirichletPrefix_prod
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Real.exp (-b*z.2^2)*‖dirichletPrefix N a (z.2-z.1)‖^2)
      ((volume.restrict (uIoc A B)).prod volume) := by
  let C : ℝ := ∑ n ∈ Finset.Ioc 0 N, ‖a n‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc : Integrable (fun _ : ℝ => C^2) (volume.restrict (uIoc A B)) := by
    change Integrable (fun _ : ℝ => C^2)
      (volume.restrict (Ioc (min A B) (max A B)))
    exact integrable_const _
  have hg := integrable_exp_neg_mul_sq hb
  have hcont : Continuous (fun z : ℝ × ℝ =>
      Real.exp (-b*z.2^2)*‖dirichletPrefix N a (z.2-z.1)‖^2) :=
    (by fun_prop : Continuous (fun z : ℝ × ℝ => Real.exp (-b*z.2^2))).mul
      (((continuous_dirichletPrefix N a).comp (by fun_prop)).norm.pow 2)
  apply (hc.mul_prod hg).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp (-b*z.2^2)*C^2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletPrefix_le N a (z.2-z.1)) 2)
        (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem intervalIntegrable_gaussianPrefixMean
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ∫ u : ℝ, Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^2) volume A B := by
  rw [intervalIntegrable_iff]
  exact (integrable_gaussian_dirichletPrefix_prod hb N a A B).integral_prod_left

theorem integral_gaussianPrefixMean_swap
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    (∫ t : ℝ in A..B, ∫ u : ℝ,
      Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^2) =
        ∫ u : ℝ, Real.exp (-b*u^2)*
          (∫ t : ℝ in A..B, ‖dirichletPrefix N a (u-t)‖^2) := by
  rw [intervalIntegral_integral_swap
    (integrable_gaussian_dirichletPrefix_prod hb N a A B)]
  simp_rw [intervalIntegral.integral_const_mul]

theorem exists_integral_gaussian_fourthPolynomial_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ, ∀ H : ℝ, 0 ≤ H →
      (∫ t : ℝ in H..2*H, ∫ u : ℝ,
        Real.exp (-98*u^2)*‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε := by
  obtain ⟨C,hC,hmean⟩ := exists_integral_sq_fourthPolynomial_le hε
  let G : ℝ := Real.sqrt (Real.pi/98)
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨C*G,mul_pos hC hG,?_⟩
  intro c hc M H hH
  rw [integral_gaussianPrefixMean_swap (by norm_num : (0:ℝ)<98)]
  let Q : ℝ := C*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε
  have hnonneg : ∀ u : ℝ, 0 ≤ Real.exp (-98*u^2)*
      (∫ t : ℝ in H..2*H, ‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) := by
    intro u
    apply mul_nonneg (Real.exp_pos _).le
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  calc
    _ ≤ ∫ u : ℝ, Real.exp (-98*u^2)*Q :=
      integral_mono_of_nonneg (Eventually.of_forall hnonneg)
        ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<98)).mul_const Q)
        (Eventually.of_forall (fun u =>
          mul_le_mul_of_nonneg_left (hmean c hc M H hH u) (Real.exp_pos _).le))
    _ = _ := by
      rw [integral_mul_const,integral_gaussian]
      dsimp [Q,G]
      ring


theorem critical_norm_matches_existing (t : ℝ) :
    MathCollab.Density.Stronger.zetaMomentCriticalNorm t =
      ‖riemannZeta (afeCriticalPoint t)‖ := by
  simp only [MathCollab.Density.Stronger.zetaMomentCriticalNorm, afeCriticalPoint,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

theorem fourth_height_power_identity {H q : ℝ} (hH : 0 < H) :
    (2*H)^(2*q)*H^(1+q)*(2*H^(1+q))^(2*q) =
      (2:ℝ)^(4*q)*H^(1+5*q+2*q^2) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH.le,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hH.le _),
    ← Real.rpow_mul hH.le]
  calc
    _ = ((2:ℝ)^(2*q)*(2:ℝ)^(2*q))*
        ((H^(2*q)*H^(1+q))*H^((1+q)*(2*q))) := by ring
    _ = (2:ℝ)^((2*q)+(2*q))*H^((2*q+(1+q))+((1+q)*(2*q))) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
        ← Real.rpow_add hH,← Real.rpow_add hH]
    _ = _ := by congr 2 <;> ring

theorem exists_fourth_dyadic_budget {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 1 ≤ H → ∀ M : ℕ,
      (2:ℝ)^M ≤ 2*H^(1+q) →
      (2*H)^(2*q)*((M:ℝ)+1)^2*
        (H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q ≤ D*H^(1+7*q) := by
  obtain ⟨A,hA,hcount⟩ := MathCollab.Density.Stronger.exists_dyadic_count_sq_le_rpow hq
  let B : ℝ := 2*(5*Real.pi+1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A*(1+2*B)*(2:ℝ)^(4*q),by positivity,?_⟩
  intro H hH M hN
  have hH0 : 0 < H := by linarith
  have hNp : 0 < (2:ℝ)^M := by positivity
  have hHH : H ≤ H^(1+q) := by
    calc
      H = H^(1:ℝ) := (Real.rpow_one H).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have hlength : H+B*(2:ℝ)^M ≤ (1+2*B)*H^(1+q) := by
    have h := mul_le_mul_of_nonneg_left hN hB.le
    nlinarith
  have hNpwr : ((2:ℝ)^M)^q*((2:ℝ)^M)^q = ((2:ℝ)^M)^(2*q) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  change (2*H)^(2*q)*((M:ℝ)+1)^2*(H+B*(2:ℝ)^M)*((2:ℝ)^M)^q ≤ _
  calc
    _ ≤ (2*H)^(2*q)*(A*((2:ℝ)^M)^q)*
        ((1+2*B)*H^(1+q))*((2:ℝ)^M)^q := by
      gcongr
      exact hcount M
    _ = A*(1+2*B)*((2*H)^(2*q)*H^(1+q))*((2:ℝ)^M)^(2*q) := by
      rw [← hNpwr]
      ring
    _ ≤ A*(1+2*B)*((2*H)^(2*q)*H^(1+q))*(2*H^(1+q))^(2*q) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hNp.le hN (by positivity)) (by positivity)
    _ = A*(1+2*B)*(2:ℝ)^(4*q)*H^(1+5*q+2*q^2) := by
      rw [mul_assoc (A*(1+2*B)),fourth_height_power_identity hH0]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH (by nlinarith)) (by positivity)


/-- The actual Gaussian averaged ordinary-divisor polynomial, with the complete
height budget already charged. No zeta or mean-value estimate is a premise. -/
theorem exists_scaled_gaussian_fourthPolynomial_le {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 1 ≤ H → ∀ M : ℕ,
      (2 : ℝ)^M ≤ 2*H^(1+q) →
      (2*H)^(2*q) *
        (∫ t : ℝ in H..2*H, ∫ u : ℝ,
          Real.exp (-98*u^2)*‖dirichletPrefix (2^M) (zetaFourthCoeff q) (u-t)‖^2) ≤
        D*H^(1+7*q) := by
  obtain ⟨C,hC,hmean⟩ := exists_integral_gaussian_fourthPolynomial_le hq
  obtain ⟨B,hB,hbudget⟩ := exists_fourth_dyadic_budget hq hq1
  refine ⟨C*B,mul_pos hC hB,?_⟩
  intro H hH M hM
  have hm := hmean q hq.le M H (by linarith)
  have hb := hbudget H hH M hM
  calc
    _ ≤ (2*H)^(2*q) *
        (C*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q) :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by linarith) _)
    _ = C*((2*H)^(2*q)*((M:ℝ)+1)^2*
        (H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q) := by ring
    _ ≤ C*(B*H^(1+7*q)) := mul_le_mul_of_nonneg_left hb hC.le
    _ = _ := by ring

end MathCollab.Density.Stronger.Fourth
