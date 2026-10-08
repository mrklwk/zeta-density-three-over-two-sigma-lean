module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected proof slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow stationary refinement; see third_party/twelfth/ATKINSON_SYMMETRIC_MANIFEST.json.
Mathlib and previously ported PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSymmetricBalance

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A derived stationary radius at and above the fourth-root width

The radius scale is T^(1/4)/sqrt(G), chosen from the same physical
parameters as the actual carrier. No error estimate is an input.
The smaller-width range is not claimed closed by this theorem.
-/

noncomputable section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSymmetricRadiusScale (T G : ℝ) : ℝ :=
  T^(1/4 : ℝ)/Real.sqrt G

theorem atkinsonSymmetricRadiusScale_pos {T G : ℝ} (hT : 0 < T) (hG : 0 < G) :
    0 < atkinsonSymmetricRadiusScale T G := by
  unfold atkinsonSymmetricRadiusScale
  positivity

theorem atkinsonSymmetricRadiusScale_sq {T G : ℝ} (hT : 0 < T) (hG : 0 < G) :
    (atkinsonSymmetricRadiusScale T G)^2 = Real.sqrt T/G := by
  unfold atkinsonSymmetricRadiusScale
  rw [div_pow,Real.sq_sqrt hG.le,← Real.rpow_natCast,← Real.rpow_mul hT.le,
    Real.sqrt_eq_rpow]
  norm_num

theorem atkinsonSymmetricRadiusScale_fourth {T G : ℝ} (hT : 0 < T) (hG : 0 < G) :
    (atkinsonSymmetricRadiusScale T G)^4 = T/G^2 := by
  rw [show (atkinsonSymmetricRadiusScale T G)^4 =
    ((atkinsonSymmetricRadiusScale T G)^2)^2 by ring,
    atkinsonSymmetricRadiusScale_sq hT hG,div_pow,Real.sq_sqrt hT.le]

theorem atkinsonSymmetricRadiusScale_balance {T G : ℝ} (hT : 1 ≤ T)
    (hlower : T^(1/4 : ℝ) ≤ G) (hupper : G ≤ Real.sqrt T) :
    1 ≤ atkinsonSymmetricRadiusScale T G ∧
      G*(atkinsonSymmetricRadiusScale T G)^2 ≤ Real.sqrt T ∧
      (atkinsonSymmetricRadiusScale T G)^4 ≤ Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 _).trans_le hlower
  have hs := Real.sqrt_nonneg T
  have hX := atkinsonSymmetricRadiusScale_pos hT0 hG
  have hXsq := atkinsonSymmetricRadiusScale_sq hT0 hG
  have hX4 := atkinsonSymmetricRadiusScale_fourth hT0 hG
  have hq : (T^(1/4 : ℝ))^2 = Real.sqrt T := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hT0.le,Real.sqrt_eq_rpow]
    norm_num
  have hGsq : Real.sqrt T ≤ G^2 := by
    nlinarith [Real.rpow_nonneg hT0.le (1/4)]
  have hproduct : G*(atkinsonSymmetricRadiusScale T G)^2 = Real.sqrt T := by
    rw [hXsq]
    field_simp
  refine ⟨?_,hproduct.le,?_⟩
  · have h1 : 1 ≤ (atkinsonSymmetricRadiusScale T G)^2 := by
      rw [hXsq]
      exact (le_div_iff₀ hG).2 (by simpa using hupper)
    nlinarith
  · rw [hX4]
    apply (div_le_iff₀ (sq_pos_of_pos hG)).2
    nlinarith [mul_le_mul_of_nonneg_left hGsq hs,Real.sq_sqrt hT0.le]

theorem exists_atkinsonPowerIntegral_fourthRoot_width (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 1 ≤ T →
      T^(1/4 : ℝ) ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 8*L ≤ G →
      |b| ≤ Real.sqrt T/100 →
      ‖atkinsonPowerIntegral T G L α b-atkinsonStationaryMain T G L α b‖ ≤
        C*G*Real.sqrt G*T^(-α-1/4) := by
  obtain ⟨C,hC,hbound⟩ := exists_atkinsonPowerIntegral_symmetric_balance α
  refine ⟨C,hC,?_⟩
  intro T G L b hT hlower hupper hL hwidth hb
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 _).trans_le hlower
  have hG1 : 1 ≤ G := (Real.one_le_rpow hT (by norm_num : (0:ℝ) ≤ 1/4)).trans hlower
  have hGT : G^2 ≤ 2*T := by nlinarith [Real.sq_sqrt hT0.le]
  obtain ⟨hX,hGX,hXS⟩ := atkinsonSymmetricRadiusScale_balance hT hlower hupper
  have h := hbound T G L b (atkinsonSymmetricRadiusScale T G) hT hG1 hGT hL hwidth
    hX hGX hXS hb
  apply h.trans_eq
  rw [Real.rpow_sub hT0]
  unfold atkinsonSymmetricRadiusScale
  field_simp

theorem exists_atkinsonPowerIntegral_fourthRoot_pair (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T →
      T^(1/4 : ℝ) ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 8*L ≤ G →
      ∀ n : ℕ, 10000*(n:ℝ) ≤ T →
      ‖atkinsonPowerIntegral T G L α (Real.sqrt n)-
        atkinsonStationaryMain T G L α (Real.sqrt n)‖ ≤
          C*G*Real.sqrt G*T^(-α-1/4) ∧
      ‖atkinsonPowerIntegral T G L α (-Real.sqrt n)-
        atkinsonStationaryMain T G L α (-Real.sqrt n)‖ ≤
          C*G*Real.sqrt G*T^(-α-1/4) := by
  obtain ⟨C,hC,hbound⟩ := exists_atkinsonPowerIntegral_fourthRoot_width α
  refine ⟨C,hC,?_⟩
  intro T G L hT hlower hupper hL hwidth n hn
  have hb := sqrt_nat_small_frequency (by linarith : 0 < T) n hn
  exact ⟨hbound T G L (Real.sqrt n) hT hlower hupper hL hwidth hb,
    hbound T G L (-Real.sqrt n) hT hlower hupper hL hwidth (by simpa only [abs_neg])⟩

end MathCollab.Density.Stronger.Atkinson
