module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_FINITE_ERROR_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLeadingFinite
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationarySeries
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFourthRootRadius
public import MathCollab.Density.Stronger.Atkinson.DivisorQuarterPrefix

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex Filter
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_norm_atkinsonLeadingTerm_sub_stationary_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T →
      T^(1/4 : ℝ) ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 8*L ≤ G →
      ∀ n : ℕ, 10000*(n:ℝ) ≤ T →
      ‖atkinsonLeadingTerm T G L n-atkinsonStationaryLeadingTerm T G L n‖ ≤
        C*G*Real.sqrt G*T^(-(1/2 : ℝ))*‖divisorDirichletTerm (1/4) n‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_atkinsonPowerIntegral_fourthRoot_pair (1/4)
  let q : ℝ := Real.sqrt Real.pi/Real.pi
  let D : ℝ := 1+‖neumannLeadingPlus‖+‖neumannLeadingMinus‖
  have hq : 0 < q := by dsimp [q]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨2*Real.pi*q*(4*Real.pi)^(-(1/2 : ℝ))*D*C,by positivity,?_⟩
  intro T G L hT hlower hupper hL hwidth n hn
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 _).trans_le hlower
  obtain ⟨hp,hm⟩ := hbound T G L hT hlower hupper hL hwidth n hn
  norm_num only [show (-(1/4 : ℝ)-1/4) = -(1/2 : ℝ) by norm_num] at hp hm
  let E : ℝ := C*G*Real.sqrt G*T^(-(1/2 : ℝ))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpair : ‖neumannLeadingPlus*(atkinsonPowerIntegral T G L (1/4) (Real.sqrt n)-
      atkinsonStationaryMain T G L (1/4) (Real.sqrt n)) +
    neumannLeadingMinus*(atkinsonPowerIntegral T G L (1/4) (-Real.sqrt n)-
      atkinsonStationaryMain T G L (1/4) (-Real.sqrt n))‖ ≤ D*E := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    apply (add_le_add (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hm (norm_nonneg _))).trans
    change ‖neumannLeadingPlus‖*E+‖neumannLeadingMinus‖*E ≤ D*E
    dsimp [D]
    nlinarith
  have he : atkinsonLeadingTerm T G L n-atkinsonStationaryLeadingTerm T G L n =
      divisorWeight n * (-(2*Real.pi) : ℂ) * (Real.sqrt Real.pi/Real.pi : ℂ) *
        (atkinsonBesselScale (1/4) n : ℂ) *
          (neumannLeadingPlus*(atkinsonPowerIntegral T G L (1/4) (Real.sqrt n)-
            atkinsonStationaryMain T G L (1/4) (Real.sqrt n)) +
          neumannLeadingMinus*(atkinsonPowerIntegral T G L (1/4) (-Real.sqrt n)-
            atkinsonStationaryMain T G L (1/4) (-Real.sqrt n))) := by
    unfold atkinsonLeadingTerm atkinsonLeadingIntegral atkinsonStationaryLeadingTerm
      atkinsonStationaryLeadingIntegral
    ring
  have hpi : ‖(-(2*Real.pi) : ℂ)‖ = 2*Real.pi := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hqn : ‖(Real.sqrt Real.pi/Real.pi : ℂ)‖ = q := by
    simp [q,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hs : ‖(atkinsonBesselScale (1/4) n : ℂ)‖ = atkinsonBesselScale (1/4) n := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (atkinsonBesselScale_nonneg _ _)]
  have hd := norm_divisorDirichletTerm_real (1/4) n
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hd
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,hpi,hqn,hs,hd]
  apply (mul_le_mul_of_nonneg_left hpair (by
    exact mul_nonneg (by positivity) (atkinsonBesselScale_nonneg _ _))).trans_eq
  dsimp [E,atkinsonBesselScale]
  norm_num only [show (-2 : ℝ)*(1/4) = -(1/2) by norm_num]
  ring

theorem exists_norm_atkinsonLeadingFiniteSum_sub_stationary_mass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T →
      T^(1/4 : ℝ) ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 8*L ≤ G →
      ∀ N : ℕ, 10000*(N:ℝ) ≤ T →
      ‖atkinsonLeadingFiniteSum T G L N-atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
        C*G*Real.sqrt G*T^(-(1/2 : ℝ))*
          ∑ n ∈ Finset.range N, ‖divisorDirichletTerm (1/4) n‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_atkinsonLeadingTerm_sub_stationary_le
  refine ⟨C,hC,?_⟩
  intro T G L hT hlower hupper hL hwidth N hN
  unfold atkinsonLeadingFiniteSum atkinsonStationaryLeadingFiniteSum
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  apply hbound T G L hT hlower hupper hL hwidth n
  have hnR : (n:ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
  linarith

theorem exists_norm_atkinsonLeadingFiniteSum_sub_stationary_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T →
      T^(1/4 : ℝ) ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 8*L ≤ G →
      ∀ N : ℕ, 10000*(N:ℝ) ≤ T →
      ‖atkinsonLeadingFiniteSum T G L N-atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
        C*G*Real.sqrt G*T^(-(1/2 : ℝ))*(N:ℝ)^(3/4+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_atkinsonLeadingFiniteSum_sub_stationary_mass_le
  obtain ⟨D,hD,hprefix⟩ := exists_sum_norm_divisorDirichletTerm_quarter_le hε
  refine ⟨C*D,by positivity,?_⟩
  intro T G L hT hlower hupper hL hwidth N hN
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 _).trans_le hlower
  apply (hbound T G L hT hlower hupper hL hwidth N hN).trans
  apply (mul_le_mul_of_nonneg_left (hprefix N) (by positivity)).trans_eq
  ring

end MathCollab.Density.Stronger.Atkinson
