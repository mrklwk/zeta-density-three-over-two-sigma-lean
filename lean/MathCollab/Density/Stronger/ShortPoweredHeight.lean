module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.ShortTaylorCover

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Fixed loss for every power k<=K; no old k<=4 restriction remains. -/
def smoothHeightConstant (K : ℕ) : ℝ := (2 : ℝ)^K*(K+1)*(192 : ℝ)^K

theorem smoothHeightConstant_pos (K : ℕ) : 0 < smoothHeightConstant K := by
  unfold smoothHeightConstant
  positivity

theorem exists_smoothPowered_height {σ T t X Y : ℝ} (j : ℤ) (e r : ℕ) {k K : ℕ}
    (hlog : 1 ≤ Real.log T) (hσ : σ ≤ 1) (hk : 0 < k) (hkK : k ≤ K)
    (hD : (smoothHalfScale j e : ℝ)^σ/(192*Real.log T) ≤
      ‖genericTaylorPolynomial (smoothShortCoefficient X Y ((2 : ℝ)^j)) (smoothHalfScale j e) r t‖) :
    ∃ l ∈ Finset.range k,
      ((2^l*(smoothHalfScale j e)^k : ℕ) : ℝ)^σ /
        (smoothHeightConstant K*(Real.log T)^K) ≤
      ‖detectingPolynomial (2^l*(smoothHalfScale j e)^k) (smoothPoweredCoefficient X Y j e r k) t‖ := by
  obtain ⟨l, hl, hh⟩ := exists_smoothTaylor_powered_piece X Y t j e r hk
  refine ⟨l, hl, ?_⟩
  have hlogpos : 0 < Real.log T := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkKR : (k : ℝ) ≤ K+1 := by exact_mod_cast (show k ≤ K+1 by omega)
  have hlK : l ≤ K := by have := Finset.mem_range.mp hl; omega
  have htwo : (2 : ℝ)^l ≤ 2^K := pow_le_pow_right₀ (by norm_num) hlK
  have hscale : ((2^l*(smoothHalfScale j e)^k : ℕ) : ℝ)^σ ≤
      (2 : ℝ)^K*((smoothHalfScale j e : ℝ)^σ)^k := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul (Nat.cast_nonneg (smoothHalfScale j e)),
      mul_comm (k : ℝ) σ, Real.rpow_mul_natCast (Nat.cast_nonneg (smoothHalfScale j e))]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hσ).trans
      (by simpa only [Real.rpow_one] using htwo)
  have hden : (k : ℝ)*(192*Real.log T)^k ≤ (K+1)*192^K*(Real.log T)^K := by
    have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ 192*Real.log T by linarith) hkK
    have hm := mul_le_mul hkKR hp (by positivity) (by positivity)
    simpa only [mul_pow, mul_assoc] using hm
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (smoothHalfScale j e : ℝ)^σ/(192*Real.log T)) hD k
  calc
    _ ≤ ((2 : ℝ)^K*((smoothHalfScale j e : ℝ)^σ)^k)/(smoothHeightConstant K*(Real.log T)^K) :=
      div_le_div_of_nonneg_right hscale (by unfold smoothHeightConstant; positivity)
    _ = ((smoothHalfScale j e : ℝ)^σ)^k/((K+1)*192^K*(Real.log T)^K) := by
      unfold smoothHeightConstant
      field_simp
    _ ≤ ((smoothHalfScale j e : ℝ)^σ)^k/((k : ℝ)*(192*Real.log T)^k) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = ((smoothHalfScale j e : ℝ)^σ/(192*Real.log T))^k/(k : ℝ) := by rw [div_pow]; ring
    _ ≤ ‖genericTaylorPolynomial (smoothShortCoefficient X Y ((2 : ℝ)^j))
        (smoothHalfScale j e) r t‖^k/(k : ℝ) := div_le_div_of_nonneg_right hpow hkpos.le
    _ ≤ _ := hh

theorem smoothHeightConstant_eventually {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∀ᶠ T : ℝ in atTop, smoothHeightConstant K*(Real.log T)^K ≤ T^η := by
  have hl := (isLittleO_log_rpow_rpow_atTop (K : ℝ) hη).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at hl
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/smoothHeightConstant K by
      exact one_div_pos.mpr (smoothHeightConstant_pos K)))] with T hT hh
  have hb := (div_lt_iff₀ (by positivity : 0 < T^η)).mp hh
  have hm := mul_le_mul_of_nonneg_left hb.le (smoothHeightConstant_pos K).le
  calc
    _ ≤ smoothHeightConstant K*((1/smoothHeightConstant K)*T^η) := hm
    _ = _ := by field_simp [(smoothHeightConstant_pos K).ne']

def normalizedSmoothPoweredCoefficient (η T X Y : ℝ) (j : ℤ) (e r k n : ℕ) : ℂ :=
  smoothPoweredCoefficient X Y j e r k n / ((T^η : ℝ) : ℂ)

theorem detectingPolynomial_normalizedSmoothPowered (η T X Y t : ℝ) (j : ℤ) (e r k L : ℕ) :
    detectingPolynomial L (normalizedSmoothPoweredCoefficient η T X Y j e r k) t =
      detectingPolynomial L (smoothPoweredCoefficient X Y j e r k) t/((T^η : ℝ) : ℂ) := by
  simp only [detectingPolynomial, normalizedSmoothPoweredCoefficient, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- One threshold normalizes every actual smooth Taylor coefficient family
and every power k<=K whose entire product support lies below T squared. -/
theorem normalizedSmoothPoweredCoefficient_eventually {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ (X Y : ℝ) (j : ℤ) (e r k : ℕ),
      0 < Y → k ≤ K → (2*(smoothHalfScale j e : ℝ))^k ≤ T^2 →
      ∀ n : ℕ, ‖normalizedSmoothPoweredCoefficient η T X Y j e r k n‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    bounded_convolution_eventually_le hη (by norm_num : (0 : ℝ) < 2) K] with T hT hb
  intro X Y j e r k hY hk hs n
  have hTpos : 0 < T := by linarith
  rw [normalizedSmoothPoweredCoefficient, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hTpos _), div_le_one (by positivity),
    smoothPoweredCoefficient, norm_conj]
  by_cases hz : ((smoothTaylorArithmetic X Y j e r)^k) n = 0
  · rw [hz, norm_zero]
    positivity
  · have hu := (finiteBlock_pow_support (smoothTaylorArithmetic_support X Y j e r) k n hz).2
    have hn : (n : ℝ) ≤ T^2 := (by exact_mod_cast hu : (n : ℝ) ≤ (2*(smoothHalfScale j e : ℝ))^k).trans hs
    exact hb (smoothTaylorArithmetic X Y j e r) (smoothTaylorArithmetic_norm_le X hY j e r) k n hk
      (by simpa only [Real.rpow_two] using hn)

/-- Height after a genuine bounded power, its k-piece split, and normalization.
The threshold precedes every original smooth scale and all coefficient indices. -/
theorem exists_normalizedSmoothPowered_height {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ (σ X Y t : ℝ) (j : ℤ) (e r k : ℕ),
      σ ≤ 1 → 0 < k → k ≤ K →
      (smoothHalfScale j e : ℝ)^σ/(192*Real.log T) ≤
        ‖genericTaylorPolynomial (smoothShortCoefficient X Y ((2 : ℝ)^j)) (smoothHalfScale j e) r t‖ →
      ∃ l ∈ Finset.range k,
        ((2^l*(smoothHalfScale j e)^k : ℕ) : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (2^l*(smoothHalfScale j e)^k)
            (normalizedSmoothPoweredCoefficient η T X Y j e r k) t‖ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    smoothHeightConstant_eventually hη K] with T hT hlog hc
  intro σ X Y t j e r k hσ hk hkK hD
  obtain ⟨l, hl, hh⟩ := exists_smoothPowered_height j e r hlog hσ hk hkK hD
  refine ⟨l, hl, ?_⟩
  have hTpos : 0 < T := by linarith
  have hden : 0 < smoothHeightConstant K*(Real.log T)^K :=
    mul_pos (smoothHeightConstant_pos K) (pow_pos (by linarith) K)
  rw [detectingPolynomial_normalizedSmoothPowered, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hTpos η)]
  calc
    _ = (((2^l*(smoothHalfScale j e)^k : ℕ) : ℝ)^σ)/T^η/T^η := by
      rw [div_div, ← Real.rpow_add hTpos, div_eq_mul_inv, ← Real.rpow_neg hTpos.le]
      congr 1
      congr 1
      ring
    _ ≤ ((((2^l*(smoothHalfScale j e)^k : ℕ) : ℝ)^σ)/(smoothHeightConstant K*(Real.log T)^K))/T^η :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hden hc) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)

end MathCollab.Density.Stronger
