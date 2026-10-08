module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.GenericTaylorFamily
public import MathCollab.Density.Stronger.SmoothPartition

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The smooth short-block coefficients precede both coordinates of every zero. -/
def smoothShortCoefficient (X Y N : ℝ) (n : ℕ) : ℂ :=
  (mollifierCoefficient X n : ℂ)*(Real.exp (-(n : ℝ)/Y) : ℂ)*
    (smoothDyadicWeight ((n : ℝ)/N) : ℂ)

theorem norm_smoothShortCoefficient_le (X N : ℝ) {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    ‖smoothShortCoefficient X Y N n‖ ≤ (n.divisors.card : ℝ) := by
  have he : Real.exp (-(n : ℝ)/Y) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hY.le)
  have hw := smoothDyadicWeight_bounds ((n : ℝ)/N)
  rw [smoothShortCoefficient, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hw.1]
  calc
    _ ≤ (n.divisors.card : ℝ)*1*1 :=
      mul_le_mul (mul_le_mul (mollifierCoefficient_norm_le X n) he
        (by positivity) (by positivity)) hw.2 hw.1 (by positivity)
    _ = _ := by ring

theorem smoothShortCoefficient_zero_of_le_half (X Y : ℝ) {N : ℝ} (hN : 0 < N)
    {n : ℕ} (hn : (n : ℝ) ≤ N/2) : smoothShortCoefficient X Y N n = 0 := by
  have hr : (n : ℝ)/N ≤ 5/8 := (div_le_iff₀ hN).mpr (by linarith)
  simp [smoothShortCoefficient, smoothDyadicWeight_zero_of_le hr]

theorem smoothShortCoefficient_zero_of_two_le (X Y : ℝ) {N : ℝ} (hN : 0 < N)
    {n : ℕ} (hn : 2*N ≤ (n : ℝ)) : smoothShortCoefficient X Y N n = 0 := by
  have hr : (3/2 : ℝ) ≤ (n : ℝ)/N := (le_div_iff₀ hN).mpr (by linarith)
  simp [smoothShortCoefficient, smoothDyadicWeight_zero_of_ge hr]

theorem smoothShortCoefficient_support (X Y : ℝ) {N : ℝ} (hN : 0 < N)
    {n : ℕ} (hn : smoothShortCoefficient X Y N n ≠ 0) :
    N/2 < (n : ℝ) ∧ (n : ℝ) < 2*N := by
  constructor
  · by_contra hh
    exact hn (smoothShortCoefficient_zero_of_le_half X Y hN (le_of_not_gt hh))
  · by_contra hh
    exact hn (smoothShortCoefficient_zero_of_two_le X Y hN (le_of_not_gt hh))

/-- A natural even scale splits exactly into (M,2M] and (2M,4M].
The original smooth weights are retained in both pieces. -/
theorem smoothShortCoefficient_tsum_split (ρ : ℂ) (X Y : ℝ) {M : ℕ} (hM : 0 < M) :
    (∑' n : ℕ, smoothShortCoefficient X Y (2*M) n*(n : ℂ)^(-ρ)) =
      genericBlock ρ (smoothShortCoefficient X Y (2*M)) M +
      genericBlock ρ (smoothShortCoefficient X Y (2*M)) (2*M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hz : ∀ n ∉ Finset.Ioc M (2*(2*M)),
      smoothShortCoefficient X Y (2*M) n*(n : ℂ)^(-ρ) = 0 := by
    intro n hn
    have hc : smoothShortCoefficient X Y (2*M) n = 0 := by
      by_contra hc
      have hs := smoothShortCoefficient_support X Y (by positivity : 0 < 2*(M : ℝ)) hc
      apply hn
      apply Finset.mem_Ioc.mpr
      constructor
      · exact_mod_cast (show (M : ℝ) < n by linarith)
      · exact_mod_cast (show (n : ℝ) ≤ 2*(2*M) by linarith)
    rw [hc, zero_mul]
  rw [tsum_eq_sum hz, ← Finset.Ioc_union_Ioc_eq_Ioc (show M ≤ 2*M by omega)
    (show 2*M ≤ 2*(2*M) by omega)]
  have hd : Disjoint (Finset.Ioc M (2*M)) (Finset.Ioc (2*M) (2*(2*M))) := by
    apply Finset.disjoint_left.mpr
    intro n h₁ h₂
    have h₁' := (Finset.mem_Ioc.mp h₁).2
    have h₂' := (Finset.mem_Ioc.mp h₂).1
    omega
  rw [Finset.sum_union hd]
  rfl

theorem smoothShortCoefficient_term_eq (ρ : ℂ) (X Y N : ℝ) (n : ℕ) :
    smoothShortCoefficient X Y N n*(n : ℂ)^(-ρ) =
      detectorTerm ρ X Y n*(smoothDyadicWeight ((n : ℝ)/N) : ℂ) := by
  dsimp [smoothShortCoefficient, detectorTerm]
  ring

theorem norm_smoothShortTaylorCoefficient_le (X N : ℝ) {Y : ℝ} (hY : 0 < Y)
    {M n : ℕ} (hM : 0 < M) (hn : n ∈ Finset.Ioc M (2*M)) (j : ℕ) :
    ‖genericTaylorCoefficient (smoothShortCoefficient X Y N) M j n‖ ≤
      (n.divisors.card : ℝ) :=
  norm_genericTaylorCoefficient_le (fun n _ => norm_smoothShortCoefficient_le X N hY n) hM hn j

/-- Compact smooth support makes every block series summable, for arbitrary rho. -/
theorem summable_smoothShortTerm (ρ : ℂ) (X Y : ℝ) {N : ℝ} (hN : 0 < N) :
    Summable (fun n : ℕ => smoothShortCoefficient X Y N n*(n : ℂ)^(-ρ)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌈2*N⌉₊+1))
  intro n hn
  have hn' : ⌈2*N⌉₊ ≤ n := by
    have hh : ⌈2*N⌉₊+1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    omega
  have hn'' : 2*N ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn')
  rw [smoothShortCoefficient_zero_of_two_le X Y hN hn'', zero_mul]

/-- Exact split for the actual detector tail, whose n=1 term was removed.
At N=2M with M>=1 the removed term has zero smooth weight. -/
theorem smoothDetector_tail_half_split (ρ : ℂ) (X Y : ℝ) {M : ℕ} (hM : 0 < M) :
    (∑' n : ℕ, detectorTerm ρ X Y (n+2)*
      (smoothDyadicWeight (((n+2 : ℕ) : ℝ)/(2*M)) : ℂ)) =
      genericBlock ρ (smoothShortCoefficient X Y (2*M)) M +
      genericBlock ρ (smoothShortCoefficient X Y (2*M)) (2*M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h0 := smoothShortCoefficient_zero_of_le_half X Y
    (by positivity : 0 < 2*(M : ℝ)) (n := 0) (by norm_num)
  have h1 := smoothShortCoefficient_zero_of_le_half X Y
    (by positivity : 0 < 2*(M : ℝ)) (n := 1) (by norm_num; linarith)
  have hs := (summable_smoothShortTerm ρ X Y (by positivity : 0 < 2*(M : ℝ))).sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, zero_mul, zero_add] at hs
  rw [← smoothShortCoefficient_tsum_split ρ X Y hM, ← hs]
  apply tsum_congr
  intro n
  exact (smoothShortCoefficient_term_eq ρ X Y (2*M) (n+2)).symm

/-- One of the two natural half blocks has half the smooth block height. -/
theorem exists_smoothShort_half (ρ : ℂ) (X Y : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ L ∈ ({M, 2*M} : Finset ℕ),
      ‖∑' n : ℕ, detectorTerm ρ X Y (n+2)*
        (smoothDyadicWeight (((n+2 : ℕ) : ℝ)/(2*M)) : ℂ)‖/2 ≤
      ‖genericBlock ρ (smoothShortCoefficient X Y (2*M)) L‖ := by
  rw [smoothDetector_tail_half_split ρ X Y hM]
  let B₁ := genericBlock ρ (smoothShortCoefficient X Y (2*M)) M
  let B₂ := genericBlock ρ (smoothShortCoefficient X Y (2*M)) (2*M)
  change ∃ L ∈ ({M, 2*M} : Finset ℕ), ‖B₁+B₂‖/2 ≤
    ‖genericBlock ρ (smoothShortCoefficient X Y (2*M)) L‖
  by_cases hh : ‖B₁+B₂‖/2 ≤ ‖B₁‖
  · exact ⟨M, by simp, hh⟩
  · refine ⟨2*M, by simp, ?_⟩
    change ‖B₁+B₂‖/2 ≤ ‖B₂‖
    have hn := norm_add_le B₁ B₂
    linarith

/-- Smooth half-block extraction with the same fixed logarithmic Taylor cutoff.
All coefficients depend only on X,Y,N,M,j; the original ordinate is preserved. -/
theorem exists_smoothShortTaylor_component (X N : ℝ) {Y T : ℝ} {M : ℕ} {ρ : ℂ}
    (hY : 0 < Y) (hT : 1 ≤ T) (hM : 0 < M) (hM' : (M : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1) {D : ℝ} (hD : 0 < D)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(4*D))
    (hblock : 1/(2*D) ≤ ‖genericBlock ρ (smoothShortCoefficient X Y N) M‖) :
    ∃ j ∈ Finset.range (detectorTaylorCutoff T+1),
      (M : ℝ)^ρ.re/(8*D) ≤
        ‖genericTaylorPolynomial (smoothShortCoefficient X Y N) M j ρ.im‖ :=
  exists_genericTaylor_component (fun n _ => norm_smoothShortCoefficient_le X N hY n)
    hT hM hM' hβ hβ' hD hsmall hblock

end MathCollab.Density.Stronger
