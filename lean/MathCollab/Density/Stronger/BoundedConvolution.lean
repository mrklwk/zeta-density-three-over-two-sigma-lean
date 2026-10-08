module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.DetectorConvolution
public import MathCollab.Density.DivisorGrowth

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Filter
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Subpower growth holds uniformly for every divisor-bounded arithmetic
function and every power up to a fixed K. -/
theorem bounded_convolution_subpower {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (f : ArithmeticFunction ℂ),
      (∀ n : ℕ, ‖f n‖ ≤ (n.divisors.card : ℝ)) →
      ∀ k n : ℕ, k ≤ K → 0 < n → ‖(f^k) n‖ ≤ A*(n : ℝ)^η := by
  have hK : (0 : ℝ) < 2*(K+1) := by positivity
  obtain ⟨C, hC, hd⟩ := divisor_card_subpower (div_pos hη hK)
  refine ⟨C^(2*(K+1)), one_le_pow₀ hC, ?_⟩
  intro f hf k n hk hn
  have hcard : (1 : ℝ) ≤ n.divisors.card := by
    have hc : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
    exact_mod_cast hc
  calc
    _ ≤ (n.divisors.card : ℝ)^(2*k) := arithmeticFunction_pow_norm_le hf k n
    _ ≤ (n.divisors.card : ℝ)^(2*(K+1)) := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(n : ℝ)^(η/(2*(K+1))))^(2*(K+1)) :=
      pow_le_pow_left₀ (by positivity) (hd n hn) _
    _ = C^(2*(K+1))*(n : ℝ)^η := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      congr 2
      push_cast
      field_simp

/-- The normalization threshold precedes every coefficient family and every
power k≤K; the ceiling bound on k cannot be replaced by the old k≤4 bound. -/
theorem bounded_convolution_eventually_le {η B : ℝ}
    (hη : 0 < η) (hB : 0 < B) (K : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ (f : ArithmeticFunction ℂ),
      (∀ n : ℕ, ‖f n‖ ≤ (n.divisors.card : ℝ)) →
      ∀ k n : ℕ, k ≤ K → (n : ℝ) ≤ T^B → ‖(f^k) n‖ ≤ T^η := by
  obtain ⟨A, hA, ha⟩ := bounded_convolution_subpower (div_pos hη (by positivity : 0 < 2*B)) K
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop A]
    with T hT hlarge
  intro f hf k n hk hn
  by_cases hn0 : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, norm_zero]
    positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hTpos : 0 < T := by linarith
  calc
    _ ≤ A*(n : ℝ)^(η/(2*B)) := ha f hf k n hk hnpos
    _ ≤ A*(T^B)^(η/(2*B)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) hn (by positivity)) (by linarith)
    _ = A*T^(η/2) := by
      rw [← Real.rpow_mul hTpos.le]
      congr 2
      field_simp
    _ ≤ T^(η/2)*T^(η/2) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = T^η := by rw [← Real.rpow_add hTpos]; congr 1; ring

end MathCollab.Density.Stronger
