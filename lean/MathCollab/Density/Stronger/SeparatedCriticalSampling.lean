module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.PhysicalTwelfthTail

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem weightedCriticalTwelfth_le_physical_interval {T u : ℝ} (hT : 1 ≤ T)
    (hu : u ∈ Icc T (2*T)) :
    weightedCriticalTwelfth 128 u ≤
      (∫ t in Icc 0 (3*T), momentDecay 128 (t-u)*zetaMomentCriticalNorm t^12) +
        (12:ℝ)^12*T^(-114 : ℝ)*Real.pi := by
  rw [weightedCriticalTwelfth_eq_translated]
  rw [← integral_add_compl measurableSet_Icc
    (integrable_translated_critical_twelfth (by norm_num : 14 ≤ 128) u)]
  exact add_le_add le_rfl (weightedCriticalTwelfth_physical_tail hT hu)

/-- Separated sampling of the actual weighted zeta means, with every tail
and integrability premise discharged. The physical moment remains literal. -/
theorem separated_weightedCriticalMean_twelfth_le_with_card {U : Finset ℝ} {T : ℝ}
    (hT : 1 ≤ T) (hU : oneSeparated U) (hslab : ∀ u ∈ U, u ∈ Icc T (2*T)) :
    (∑ u ∈ U, (weightedCriticalMean 128 u)^12) ≤
      Real.pi^11 * (separationMass * ∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) +
        Real.pi^11 * ((U.card : ℝ)*(12:ℝ)^12*T^(-114 : ℝ)*Real.pi) := by
  calc
    _ ≤ ∑ u ∈ U, Real.pi^11*weightedCriticalTwelfth 128 u :=
      Finset.sum_le_sum (fun u _ => weightedCriticalMean_twelfth_le (by norm_num : 14 ≤ 128) u)
    _ = Real.pi^11 * ∑ u ∈ U, weightedCriticalTwelfth 128 u := by rw [Finset.mul_sum]
    _ ≤ Real.pi^11 * ∑ u ∈ U,
        ((∫ t in Icc 0 (3*T), momentDecay 128 (t-u)*zetaMomentCriticalNorm t^12) +
          (12:ℝ)^12*T^(-114 : ℝ)*Real.pi) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun u hu => weightedCriticalTwelfth_le_physical_interval hT (hslab u hu))
    _ = Real.pi^11 * ((∑ u ∈ U, ∫ t in Icc 0 (3*T),
          momentDecay 128 (t-u)*zetaMomentCriticalNorm t^12) +
          (U.card : ℝ)*((12:ℝ)^12*T^(-114 : ℝ)*Real.pi)) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
    _ ≤ Real.pi^11 * ((separationMass * ∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) +
          (U.card : ℝ)*((12:ℝ)^12*T^(-114 : ℝ)*Real.pi)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (separated_critical_twelfth_on_interval (by norm_num : 2 ≤ 128) hU 0 (3*T)) le_rfl
    _ = _ := by ring

theorem separated_card_in_height_slab {U : Finset ℝ} {T : ℝ}
    (hT : 1 ≤ T) (hU : oneSeparated U) (hslab : ∀ u ∈ U, u ∈ Icc T (2*T)) :
    (U.card : ℝ) ≤ 2*T := by
  have hspan : intervalSpan U ≤ T := by
    apply intervalSpan_le_of_forall (by linarith : 0 ≤ T)
    intro u hu v hv
    have huu := hslab u hu
    have hvv := hslab v hv
    exact abs_le.mpr ⟨by linarith [huu.1,huu.2,hvv.1,hvv.2],
      by linarith [huu.1,huu.2,hvv.1,hvv.2]⟩
  have hc := separated_card_le_localDiameter hU
  unfold localDiameter at hc
  linarith

/-- The tail cardinality is removed by actual one-separated packing. -/
theorem separated_weightedCriticalMean_twelfth_le {U : Finset ℝ} {T : ℝ}
    (hT : 1 ≤ T) (hU : oneSeparated U) (hslab : ∀ u ∈ U, u ∈ Icc T (2*T)) :
    (∑ u ∈ U, (weightedCriticalMean 128 u)^12) ≤
      Real.pi^11 * separationMass * (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) +
        (2*(12:ℝ)^12*Real.pi^12)*T^(-113 : ℝ) := by
  have hbase := separated_weightedCriticalMean_twelfth_le_with_card hT hU hslab
  have hc := separated_card_in_height_slab hT hU hslab
  have hTp : 0 < T := by linarith
  have hp : T*T^(-114 : ℝ) = T^(-113 : ℝ) := by
    simpa only [Real.rpow_one, show (1:ℝ)+(-114) = -113 by norm_num] using
      (Real.rpow_add hTp (1:ℝ) (-114)).symm
  have htail : Real.pi^11*((U.card : ℝ)*(12:ℝ)^12*T^(-114 : ℝ)*Real.pi) ≤
      (2*(12:ℝ)^12*Real.pi^12)*T^(-113 : ℝ) := by
    calc
      _ ≤ Real.pi^11*((2*T)*(12:ℝ)^12*T^(-114 : ℝ)*Real.pi) := by gcongr
      _ = (2*(12:ℝ)^12*Real.pi^12)*(T*T^(-114 : ℝ)) := by ring
      _ = _ := by rw [hp]
  exact hbase.trans (by simpa only [mul_assoc] using add_le_add le_rfl htail)

end MathCollab.Density.Stronger
