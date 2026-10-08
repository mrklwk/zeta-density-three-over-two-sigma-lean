module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected proof slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow stationary refinement; see third_party/twelfth/ATKINSON_SYMMETRIC_MANIFEST.json.
Mathlib and previously ported PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSymmetricReduction
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSampleGeometry

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Natural physical balance for the symmetric stationary error

The improved radius constraints are G X^2 <= sqrt(T), X^4 <= sqrt(T).
They replace the earlier cubic/fifth-power balance. Both physical
frequency signs are handled by the same actual-source theorem.
-/

noncomputable section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonSymmetricError_le_physical {T G H b : ℝ}
    (hT : 0 < T) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hb : |b| ≤ Real.sqrt T/100) :
    atkinsonSymmetricError T b (G/Real.sqrt T) H ≤
      4/(H*Real.pi) + 4*G^2*H^3/T + 216*G*H^5/T +
        1296*H^5/T + 11664*H^7/T := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T/(2*Real.pi)) b
  have hlo := (atkinsonSaddleRoot_small_frequency hT hb).1
  have h3 : 8*(G/Real.sqrt T)*T*H^5/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 ≤
      8*(G/Real.sqrt T)*T*H^5/(Real.sqrt T/3)^3 := by gcongr
  have h4 : 16*T*H^5/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^4 ≤
      16*T*H^5/(Real.sqrt T/3)^4 := by gcongr
  have h6 : 16*T^2*H^7/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^6 ≤
      16*T^2*H^7/(Real.sqrt T/3)^6 := by gcongr
  unfold atkinsonSymmetricError
  calc
    _ ≤ 4/(H*Real.pi) + 4*(G/Real.sqrt T)^2*H^3 +
        8*(G/Real.sqrt T)*T*H^5/(Real.sqrt T/3)^3 +
        16*T*H^5/(Real.sqrt T/3)^4 +
        16*T^2*H^7/(Real.sqrt T/3)^6 := by linarith
    _ = _ := by
      have h4 : (Real.sqrt T)^4 = T^2 := by
        rw [show (Real.sqrt T)^4 = ((Real.sqrt T)^2)^2 by ring,Real.sq_sqrt hT.le]
      have h6 : (Real.sqrt T)^6 = T^3 := by
        rw [show (Real.sqrt T)^6 = ((Real.sqrt T)^2)^3 by ring,Real.sq_sqrt hT.le]
      have he3 : 8*(G/Real.sqrt T)*T*H^5/(Real.sqrt T/3)^3 = 216*G*H^5/T := by
        calc
          _ = 216*G*H^5*T/(Real.sqrt T)^4 := by ring
          _ = _ := by rw [h4]; field_simp
      have he4 : 16*T*H^5/(Real.sqrt T/3)^4 = 1296*H^5/T := by
        calc
          _ = 1296*T*H^5/(Real.sqrt T)^4 := by ring
          _ = _ := by rw [h4]; field_simp
      have he6 : 16*T^2*H^7/(Real.sqrt T/3)^6 = 11664*H^7/T := by
        calc
          _ = 11664*T^2*H^7/(Real.sqrt T)^6 := by ring
          _ = _ := by rw [h6]; field_simp
      rw [he3,he4,he6,div_pow,Real.sq_sqrt hT.le]
      ring

theorem atkinsonSymmetric_error_le_of_power_balance {T G X : ℝ}
    (hT : 0 < T) (hG : 0 ≤ G) (hX : 1 ≤ X)
    (hGX : G*X^2 ≤ Real.sqrt T) (hXS : X^4 ≤ Real.sqrt T) :
    4/((X/12)*Real.pi) + 4*G^2*(X/12)^3/T + 216*G*(X/12)^5/T +
      1296*(X/12)^5/T + 11664*(X/12)^7/T ≤ 20/X := by
  have hX0 : 0 < X := by linarith
  have hs := Real.sqrt_nonneg T
  have hsq := Real.sq_sqrt hT.le
  have hg2 : G^2*X^4 ≤ T := by nlinarith [sq_le_sq₀ (by positivity : 0 ≤ G*X^2) hs |>.2 hGX]
  have hg6 : G*X^6 ≤ T := by nlinarith [mul_le_mul hGX hXS (by positivity) hs]
  have hx8 : X^8 ≤ T := by nlinarith [sq_le_sq₀ (by positivity : 0 ≤ X^4) hs |>.2 hXS]
  have hx6 : X^6 ≤ T := (pow_le_pow_right₀ hX (by norm_num : (6:ℕ) ≤ 8)).trans hx8
  have hfirst : 4/((X/12)*Real.pi) ≤ 16/X := by
    apply (div_le_div_iff₀ (by positivity) hX0).2
    nlinarith [Real.pi_gt_three]
  have hsecond : 4*G^2*(X/12)^3/T ≤ 1/X := by
    apply (div_le_div_iff₀ hT hX0).2
    nlinarith
  have hthird : 216*G*(X/12)^5/T ≤ 1/X := by
    apply (div_le_div_iff₀ hT hX0).2
    nlinarith
  have hfourth : 1296*(X/12)^5/T ≤ 1/X := by
    apply (div_le_div_iff₀ hT hX0).2
    nlinarith
  have hfifth : 11664*(X/12)^7/T ≤ 1/X := by
    apply (div_le_div_iff₀ hT hX0).2
    nlinarith
  calc
    _ ≤ 16/X + 1/X + 1/X + 1/X + 1/X := by linarith
    _ = _ := by ring

theorem exists_atkinsonPowerIntegral_symmetric_balance (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b X : ℝ, 1 ≤ T → 1 ≤ G →
      G^2 ≤ 2*T → 1 ≤ L → 8*L ≤ G → 1 ≤ X →
      G*X^2 ≤ Real.sqrt T → X^4 ≤ Real.sqrt T →
      |b| ≤ Real.sqrt T/100 →
      ‖atkinsonPowerIntegral T G L α b-atkinsonStationaryMain T G L α b‖ ≤
        C*G*T^(-α)/X := by
  obtain ⟨C,hC,hbound⟩ := exists_atkinsonPowerIntegral_symmetric_approximation α
  refine ⟨20*C,by positivity,?_⟩
  intro T G L b X hT hG hGT hL hwidth hX hGX hXS hb
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hXpow : X ≤ X^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hX (by norm_num : (1:ℕ) ≤ 4)
  have hXle : X ≤ Real.sqrt T := hXpow.trans hXS
  obtain ⟨hleft,hright,hwindow⟩ :=
    atkinsonSaddleRoot_small_frequency_window hT0 hb (show X/12 ≤ Real.sqrt T/12 by linarith)
  have h := hbound T G L b (X/12) hT0 hG hGT hL hwidth (by positivity) hleft hright hwindow
  have he := (atkinsonSymmetricError_le_physical (G := G) (H := X/12)
    hT0 (by linarith) (by positivity) hb).trans
    (atkinsonSymmetric_error_le_of_power_balance hT0 (by linarith) hX hGX hXS)
  apply h.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ?_)
  ring

end MathCollab.Density.Stronger.Atkinson
