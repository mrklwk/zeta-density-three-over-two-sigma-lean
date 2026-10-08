module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.DetectorBlockExpansion
public import MathCollab.Density.DetectorFamilyScales

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Fixed coefficients depending on the base coefficients and scale, never on a zero. -/
def genericTaylorCoefficient (a : ℕ → ℂ) (N j n : ℕ) : ℂ :=
  a n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j)

def genericTaylorPolynomial (a : ℕ → ℂ) (N j : ℕ) (t : ℝ) : ℂ :=
  detectingPolynomial N (genericTaylorCoefficient a N j) (-t)

def genericBlock (ρ : ℂ) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n * (n : ℂ)^(-ρ)

theorem norm_genericTaylorCoefficient_le {a : ℕ → ℂ} {N n : ℕ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ)) (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2*N)) (j : ℕ) :
    ‖genericTaylorCoefficient a N j n‖ ≤ (n.divisors.card : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : (N : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
  have hhi : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hr : |2*(n : ℝ)/N-3| ≤ 1 := by
    apply abs_le.mpr
    have hl : (2 : ℝ) ≤ 2*(n : ℝ)/N := (le_div_iff₀ hNpos).2 (by linarith)
    have hh : 2*(n : ℝ)/N ≤ 4 := (div_le_iff₀ hNpos).2 (by linarith)
    constructor <;> linarith
  rw [genericTaylorCoefficient, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hp : |2*(n : ℝ)/N-3|^j ≤ 1 := pow_le_one₀ (abs_nonneg _) hr
  exact (mul_le_mul (ha n hn) hp (by positivity) (by positivity)).trans_eq (mul_one _)

/-- Uniform in the Taylor index and ordinate, before any beta approximation. -/
theorem norm_genericTaylorPolynomial_le {a : ℕ → ℂ} {N : ℕ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ)) (hN : 0 < N) (j : ℕ) (t : ℝ) :
    ‖genericTaylorPolynomial a N j t‖ ≤ 2*(N : ℝ)^2 := by
  unfold genericTaylorPolynomial detectingPolynomial
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N (2*N), ‖genericTaylorCoefficient a N j n * dirichletPhase ((n : ℝ)/N) (-t)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc N (2*N), (2*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_dirichletPhase, mul_one]
      have hc : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
      have hn' : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
      exact (norm_genericTaylorCoefficient_le ha hN hn j).trans (hc.trans hn')
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      rw [show 2*N-N = N by omega]
      ring

/-- The tail of the actual fixed polynomial family has geometric decay.
Identifying its full weighted series with the beta-dependent block is separate. -/
theorem norm_genericTaylor_tail_le {a : ℕ → ℂ} {β : ℝ} {N : ℕ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ)) (hN : 0 < N) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (J : ℕ) (t : ℝ) :
    ‖∑' j : ℕ, (detectorTaylorWeight β (j+J) : ℂ)*genericTaylorPolynomial a N (j+J) t‖ ≤
      3*(N : ℝ)^2*(1/3 : ℝ)^J := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1)).mul_left (2*(N : ℝ)^2*(1/3 : ℝ)^J)
  have hb : ∀ j : ℕ, ‖(detectorTaylorWeight β (j+J) : ℂ)*genericTaylorPolynomial a N (j+J) t‖ ≤
      (2*(N : ℝ)^2*(1/3 : ℝ)^J)*(1/3 : ℝ)^j := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (1/3 : ℝ)^(j+J)*(2*(N : ℝ)^2) :=
        mul_le_mul (abs_detectorTaylorWeight_le hβ hβ' _) (norm_genericTaylorPolynomial_le ha hN _ _)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hn := hg.summable.of_nonneg_of_le (fun j => norm_nonneg _) hb
  calc
    _ ≤ ∑' j : ℕ, ‖(detectorTaylorWeight β (j+J) : ℂ)*genericTaylorPolynomial a N (j+J) t‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := (hn.tsum_le_tsum hb hg.summable).trans_eq (by rw [hg.tsum_eq]; norm_num; ring)

def normalizedGenericBlock (ρ : ℂ) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n *
    ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im)

/-- Exact rescaling, including the unit phase of N; no ordinate is shifted. -/
theorem genericBlock_eq_normalized {N : ℕ} (hN : 0 < N) (ρ : ℂ) (a : ℕ → ℂ) :
    genericBlock ρ a N = (N : ℂ)^(-ρ)*normalizedGenericBlock ρ a N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [genericBlock, normalizedGenericBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_trans hN (Finset.mem_Ioc.mp hn).1)
  have hsplit : (n : ℂ)^(-ρ) = (N : ℂ)^(-ρ)*(((n : ℝ)/N : ℝ) : ℂ)^(-ρ) := by
    have hh := Complex.mul_cpow_ofReal_nonneg hNpos.le (div_nonneg hnpos.le hNpos.le) (-ρ)
    have hm : ((N : ℝ) : ℂ)*(((n : ℝ)/N : ℝ) : ℂ) = (n : ℂ) := by
      push_cast
      field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast hN.ne']
    rw [hm, Complex.ofReal_natCast] at hh
    exact hh
  rw [hsplit, cpow_neg_eq_real_phase (div_pos hnpos hNpos)]
  ring

theorem norm_normalizedGenericBlock {N : ℕ} (hN : 0 < N) (ρ : ℂ) (a : ℕ → ℂ) :
    ‖normalizedGenericBlock ρ a N‖ = (N : ℝ)^ρ.re*‖genericBlock ρ a N‖ := by
  rw [genericBlock_eq_normalized hN, norm_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re]
  rw [← mul_assoc, ← Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]
  simp

/-- Genuine summation and finite-sum interchange for the fixed Taylor family. -/
theorem hasSum_genericTaylorPolynomial {N : ℕ} (hN : 0 < N) (ρ : ℂ) (a : ℕ → ℂ) :
    HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*genericTaylorPolynomial a N j ρ.im)
      ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*normalizedGenericBlock ρ a N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ n ∈ Finset.Ioc N (2*N),
      HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*
        (a n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j) *
          dirichletPhase ((n : ℝ)/N) (-ρ.im)))
        ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*(a n *
          ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im))) := by
    intro n hn
    have hlo : (1 : ℝ) ≤ (n : ℝ)/N := (le_div_iff₀ hNpos).2 (by simpa using (show (N : ℝ) ≤ n by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le))
    have hhi : (n : ℝ)/N ≤ 2 := (div_le_iff₀ hNpos).2 (by exact_mod_cast (Finset.mem_Ioc.mp hn).2)
    have hs := hasSum_detector_binomial (β := ρ.re) hlo hhi
    have he : (2*((n : ℝ)/N)/3)^(-ρ.re) = (3/2 : ℝ)^ρ.re*((n : ℝ)/N)^(-ρ.re) := by
      rw [show 2*((n : ℝ)/N)/3 = ((n : ℝ)/N)/(3/2) by ring,
        Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (show (0 : ℝ) ≤ 3/2 by norm_num), div_inv_eq_mul]
      ring
    rw [he] at hs
    have hc := (hs.map Complex.ofRealCLM Complex.continuous_ofReal).mul_left
      (a n*dirichletPhase ((n : ℝ)/N) (-ρ.im))
    convert hc using 1
    · funext j
      simp only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow]
      push_cast
      ring
    · simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]
      ring
  have hs := hasSum_sum hterm
  convert hs using 1
  · funext j
    simp [genericTaylorPolynomial, detectingPolynomial, genericTaylorCoefficient, Finset.mul_sum]
  · rw [normalizedGenericBlock, Finset.mul_sum]

/-- The full Taylor combination is at least the beta-rescaled original block. -/
theorem norm_genericTaylor_tsum_ge {N : ℕ} (hN : 0 < N) {ρ : ℂ} (hβ : 0 ≤ ρ.re) (a : ℕ → ℂ) :
    (N : ℝ)^ρ.re*‖genericBlock ρ a N‖ ≤
      ‖∑' j : ℕ, (detectorTaylorWeight ρ.re j : ℂ)*genericTaylorPolynomial a N j ρ.im‖ := by
  rw [(hasSum_genericTaylorPolynomial hN ρ a).tsum_eq, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_normalizedGenericBlock hN]
  have hpow : (1 : ℝ) ≤ (3/2 : ℝ)^ρ.re := Real.one_le_rpow (by norm_num) hβ
  nlinarith [show 0 ≤ (N : ℝ)^ρ.re*‖genericBlock ρ a N‖ by positivity]


/-- Quantitative tail control at the actual family cutoff. -/
theorem norm_fixedGenericTaylor_tail_le {a : ℕ → ℂ} {T : ℝ} {N : ℕ} {ρ : ℂ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ))
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    ‖∑' j : ℕ, (detectorTaylorWeight ρ.re (j+(detectorTaylorCutoff T+1)) : ℂ)*
      genericTaylorPolynomial a N (j+(detectorTaylorCutoff T+1)) ρ.im‖ ≤ 3*T^(-1 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hp : (1/3 : ℝ)^(detectorTaylorCutoff T+1) ≤ T^(-5 : ℝ) := by
    have hh : (1/3 : ℝ)^(detectorTaylorCutoff T+1) ≤ (1/3 : ℝ)^(detectorTaylorCutoff T) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1/3 by norm_num) (detectorTaylorCutoff T)]
    exact hh.trans (detectorTaylorCutoff_geometric_le hT)
  calc
    _ ≤ 3*(N : ℝ)^2*(1/3 : ℝ)^(detectorTaylorCutoff T+1) :=
      norm_genericTaylor_tail_le ha hN hβ hβ' _ _
    _ ≤ 3*(T^2)^2*T^(-5 : ℝ) := by gcongr
    _ = 3*T^(-1 : ℝ) := by
      rw [show (T^2)^2 = T^4 by ring, ← Real.rpow_natCast T 4, mul_assoc, ← Real.rpow_add hTpos]
      norm_num

/-- The fixed family has the full block height, up to an absolute constant. -/
theorem exists_genericTaylor_component {a : ℕ → ℂ} {T : ℝ} {N : ℕ} {ρ : ℂ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ))
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    {D : ℝ} (hD : 0 < D)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(4*D))
    (hblock : 1/(2*D) ≤ ‖genericBlock ρ a N‖) :
    ∃ j ∈ Finset.range (detectorTaylorCutoff T+1),
      (N : ℝ)^ρ.re/(8*D) ≤ ‖genericTaylorPolynomial a N j ρ.im‖ := by
  let J := detectorTaylorCutoff T
  let W := fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*genericTaylorPolynomial a N j ρ.im
  have hp : 1 ≤ (N : ℝ)^ρ.re := Real.one_le_rpow (by exact_mod_cast hN) hβ
  have hfull := norm_genericTaylor_tsum_ge hN hβ a
  have ht := (norm_fixedGenericTaylor_tail_le ha hT hN hN' hβ hβ').trans hsmall
  have hs := (hasSum_genericTaylorPolynomial hN ρ a).summable.sum_add_tsum_nat_add (J+1)
  have hnorm : ‖∑' j, W j‖ ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ + ‖∑' j, W (j+(J+1))‖ := by
    change (∑ j ∈ Finset.range (J+1), W j)+(∑' j, W (j+(J+1))) = (∑' j, W j) at hs
    rw [← hs]
    exact norm_add_le _ _
  have hpartial : (N : ℝ)^ρ.re/(4*D) ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ := by
    have hb := mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (Nat.cast_nonneg N) ρ.re)
    have ht' : ‖∑' j, W (j+(J+1))‖ ≤ (N : ℝ)^ρ.re/(4*D) := by
      exact ht.trans ((div_le_div_iff_of_pos_right (by positivity)).mpr hp)
    change (N : ℝ)^ρ.re*‖genericBlock ρ a N‖ ≤ ‖∑' j, W j‖ at hfull
    change (N : ℝ)^ρ.re*(1/(2*D)) ≤ _ at hb
    have halg : (N : ℝ)^ρ.re*(1/(2*D)) = 2*((N : ℝ)^ρ.re/(4*D)) := by ring
    rw [halg] at hb
    linarith
  obtain ⟨j, hj, hlarge⟩ := exists_large_taylor_component hβ hβ' J (genericTaylorPolynomial a N · ρ.im)
  refine ⟨j, hj, ?_⟩
  have hh := div_le_div_of_nonneg_right hpartial (by norm_num : (0 : ℝ) ≤ 2)
  change ‖∑ j ∈ Finset.range (J+1), W j‖/2 ≤ _ at hlarge
  exact (show (N : ℝ)^ρ.re/(8*D) = ((N : ℝ)^ρ.re/(4*D))/2 by ring).trans_le (hh.trans hlarge)


end MathCollab.Density.Stronger
