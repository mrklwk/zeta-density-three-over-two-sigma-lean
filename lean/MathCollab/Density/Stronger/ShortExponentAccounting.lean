module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.ShortPoweredFamily
public import MathCollab.Density.DensityExponentAccounting

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The stronger lower scale still exceeds sqrt(T), preserving the original
positive-kappa large-values margin. -/
theorem sqrt_le_stronger_lower_scale {σ T : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1) (hT : 1 ≤ T) :
    Real.sqrt T ≤ T^(lowerExponent σ) := by
  have ha : (1/2 : ℝ) ≤ lowerExponent σ := by
    unfold lowerExponent
    exact (le_div_iff₀ (by positivity : 0 < 2*σ)).mpr (by linarith)
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hT ha

/-- Full hypotheses of the certified large-values theorem at the unchanged
comparison height H=32T log(T)^2, for every fixed short-family member. -/
theorem smoothPoweredFamily_largeValues_admissible {σ η κ : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ ≤ 1) (hη : 0 < η)
    (hmargin : 3/4+κ ≤ σ-4*η) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop, 2 ≤ densityAmbient T ∧ 2*T ≤ T+densityAmbient T ∧
      ∀ q ∈ smoothPoweredIndices σ δ T,
        0 < smoothPoweredFamilyScale q ∧
        0 < (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ∧
        (densityAmbient T)^(1/3 : ℝ) ≤ (smoothPoweredFamilyScale q : ℝ) ∧
        (smoothPoweredFamilyScale q : ℝ) ≤ densityAmbient T ∧
        (smoothPoweredFamilyScale q : ℝ)^(3/4+κ) ≤
          (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ∧
        ∀ n ∈ Finset.Ioc (smoothPoweredFamilyScale q) (2*smoothPoweredFamilyScale q),
          ‖smoothPoweredFamilyCoefficient η σ δ T q n‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    densityAmbient_eventually_cubeRoot_le, smoothPoweredFamily_admissible hσ hη δ]
    with T hT hlog hroot hadm
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hH : T ≤ densityAmbient T := by unfold densityAmbient; nlinarith [sq_nonneg (Real.log T-1)]
  refine ⟨hT.trans hH, by linarith, ?_⟩
  intro q hq
  obtain ⟨hlo, _, hhi, hc⟩ := hadm q hq
  have hL := smoothPoweredFamilyScale_pos q
  have hsqrt := (sqrt_le_stronger_lower_scale (by linarith : 0 < σ) hσ' hT1).trans hlo
  have hLreal : (0 : ℝ) < smoothPoweredFamilyScale q := by exact_mod_cast hL
  refine ⟨hL, by positivity, hroot.trans hsqrt, hhi.trans hH, ?_, fun n _ => hc n⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL) hmargin).trans
    (detectorHeight_ge_scale hTpos hsqrt hη.le)

/-- The positive scale exponent uses 2^K T^c, while the negative scale
exponent uses T^a. Both give exactly densityExponent(sigma), not 2(1-sigma). -/
theorem smooth_largeValue_term_le {T L σ η : ℝ} (K : ℕ)
    (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T) (hσ : 3/4 < σ) (hσ' : σ ≤ 1)
    (hη : 0 ≤ η) (hlo : T^(lowerExponent σ) ≤ L)
    (hhi : L ≤ (2 : ℝ)^K*T^(smoothingExponent σ)) :
    L^2/(L^σ*T^(-2*η))^2+L^3*Real.sqrt (densityAmbient T)/(L^σ*T^(-2*η))^4 ≤
      ((2 : ℝ)^K+32)*Real.log T*T^(densityExponent σ+8*η) := by
  have hTpos : 0 < T := by linarith
  have hLpos : 0 < L := (Real.rpow_pos_of_pos hTpos _).trans_le hlo
  have hid := short_exponent_identities (show 0 < σ by linarith)
  have hlow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hTpos (lowerExponent σ)) hlo
    (show 3-4*σ ≤ 0 by linarith)
  have hhigh : L^(2-2*σ) ≤ (2 : ℝ)^K*T^(densityExponent σ) := by
    have hb := Real.rpow_le_rpow hLpos.le hhi (show 0 ≤ 2-2*σ by linarith)
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hTpos.le] at hb
    have hpow : ((2 : ℝ)^K)^(2-2*σ) ≤ (2 : ℝ)^K := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (show 2-2*σ ≤ 1 by linarith)
    have he : smoothingExponent σ*(2-2*σ) = densityExponent σ := by nlinarith [hid.1]
    rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hpow (by positivity))
  have hsqrt : Real.sqrt (densityAmbient T) ≤ 32*T^(1/2 : ℝ)*Real.log T := by
    simpa only [Real.sqrt_eq_rpow] using densityAmbient_small_rpow hT hlog
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1/2)
  have he₁ : T^(densityExponent σ)*T^(4*η) = T^(densityExponent σ+4*η) :=
    (Real.rpow_add hTpos _ _).symm
  have he₂ : (T^(lowerExponent σ))^(3-4*σ)*T^(1/2 : ℝ)*T^(8*η) =
      T^(densityExponent σ+8*η) := by
    rw [← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
    congr 1
    nlinarith [hid.2]
  have hp : T^(densityExponent σ+4*η) ≤ T^(densityExponent σ+8*η) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hfirst : L^2/(L^σ*T^(-2*η))^2 ≤ (2 : ℝ)^K*Real.log T*T^(densityExponent σ+8*η) := by
    rw [normalizedHeight_quotient hTpos hLpos]
    norm_num only [Nat.cast_ofNat]
    have hh := mul_le_mul_of_nonneg_right hhigh (show 0 ≤ T^(4*η) by positivity)
    calc
      _ = L^(2-2*σ)*T^(4*η) := by congr 1 <;> congr 1 <;> ring
      _ ≤ ((2 : ℝ)^K*T^(densityExponent σ))*T^(4*η) := hh
      _ = (2 : ℝ)^K*T^(densityExponent σ+4*η) := by rw [← he₁]; ring
      _ ≤ (2 : ℝ)^K*T^(densityExponent σ+8*η) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by nlinarith [show 0 ≤ (2 : ℝ)^K*T^(densityExponent σ+8*η) by positivity]
  have hsecond : L^3*Real.sqrt (densityAmbient T)/(L^σ*T^(-2*η))^4 ≤
      32*Real.log T*T^(densityExponent σ+8*η) := by
    rw [mul_div_right_comm, normalizedHeight_quotient hTpos hLpos]
    norm_num only [Nat.cast_ofNat]
    have hh := mul_le_mul hlow hsqrt (Real.sqrt_nonneg _) (by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ T^(8*η) by positivity)
    calc
      _ = (L^(3-4*σ)*Real.sqrt (densityAmbient T))*T^(8*η) := by
        rw [show 3-σ*4 = 3-4*σ by ring, show 2*η*4 = 8*η by ring]
        ring
      _ ≤ ((T^(lowerExponent σ))^(3-4*σ)*(32*T^(1/2 : ℝ)*Real.log T))*T^(8*η) := hh'
      _ = 32*Real.log T*T^(densityExponent σ+8*η) := by rw [← he₂]; ring
  nlinarith

/-- Full explicit 12 eta budget for the actual finite short family:
8 eta in the quotient terms, 2 eta for H^eta, and 2 eta for four logarithms. -/
theorem smooth_family_sum_eventually {η σ : ℝ}
    (hη : 0 < η) (hσ : 3/4 < σ) (hσ' : σ ≤ 1) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      Real.log (2*T)*(densityAmbient T)^η*
        (∑ q ∈ smoothPoweredIndices σ δ T,
          ((smoothPoweredFamilyScale q : ℝ)^2/
              ((smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η))^2+
            (smoothPoweredFamilyScale q : ℝ)^3*Real.sqrt (densityAmbient T)/
              ((smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η))^4)) ≤
        (288*(smoothPowerBound σ δ : ℝ)^2*((2 : ℝ)^(smoothPowerBound σ δ)+32))*
          T^(densityExponent σ+12*η) := by
  let K := smoothPowerBound σ δ
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    densityAmbient_eventually_le_sq, density_logarithms_eventually hη,
    smoothPoweredIndices_card_eventually hσ δ, smoothPoweredFamily_admissible hσ hη δ]
    with T hT hlog hH hlogpow hcard hadm
  have hTpos : 0 < T := by linarith
  have hsum : (∑ q ∈ smoothPoweredIndices σ δ T,
      ((smoothPoweredFamilyScale q : ℝ)^2/((smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η))^2+
        (smoothPoweredFamilyScale q : ℝ)^3*Real.sqrt (densityAmbient T)/
          ((smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η))^4)) ≤
      (144*(K : ℝ)^2*((2 : ℝ)^K+32))*(Real.log T)^3*T^(densityExponent σ+8*η) := by
    calc
      _ ≤ ∑ _q ∈ smoothPoweredIndices σ δ T, ((2 : ℝ)^K+32)*Real.log T*T^(densityExponent σ+8*η) := by
        apply Finset.sum_le_sum
        intro q hq
        have hs := hadm q hq
        exact smooth_largeValue_term_le K (by linarith) hlog hσ hσ' hη.le hs.1 hs.2.1
      _ = ((smoothPoweredIndices σ δ T).card : ℝ)*(((2 : ℝ)^K+32)*Real.log T*T^(densityExponent σ+8*η)) := by simp
      _ ≤ (144*(K : ℝ)^2*(Real.log T)^2)*(((2 : ℝ)^K+32)*Real.log T*T^(densityExponent σ+8*η)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hHpow : (densityAmbient T)^η ≤ T^(2*η) := by
    have hh := Real.rpow_le_rpow (show 0 ≤ densityAmbient T by unfold densityAmbient; positivity) hH hη.le
    rw [← Real.rpow_natCast_mul hTpos.le] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hlogs : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    linarith
  have hHnonneg : 0 ≤ densityAmbient T := by unfold densityAmbient; positivity
  have hmul := mul_le_mul (mul_le_mul hlogs hHpow (by positivity) (by positivity)) hsum
    (by positivity) (by positivity)
  calc
    _ ≤ (2*Real.log T*T^(2*η))*
        ((144*(K : ℝ)^2*((2 : ℝ)^K+32))*(Real.log T)^3*T^(densityExponent σ+8*η)) := hmul
    _ = (288*(K : ℝ)^2*((2 : ℝ)^K+32))*(Real.log T)^4*
        (T^(2*η)*T^(densityExponent σ+8*η)) := by ring
    _ ≤ (288*(K : ℝ)^2*((2 : ℝ)^K+32))*T^(2*η)*
        (T^(2*η)*T^(densityExponent σ+8*η)) := by gcongr
    _ = _ := by
      rw [mul_assoc (288*(K : ℝ)^2*((2 : ℝ)^K+32)), ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
      congr 1
      congr 1
      ring

end MathCollab.Density.Stronger
