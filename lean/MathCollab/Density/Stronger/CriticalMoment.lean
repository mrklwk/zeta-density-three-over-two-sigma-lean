module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.TruncatedLayerCake
public import Mathlib.NumberTheory.LSeries.RiemannZeta

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Filter Set
open scoped Interval ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

def zetaMomentCriticalNorm (t : ℝ) : ℝ :=
  ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖

theorem continuous_zetaMomentCriticalNorm : Continuous zetaMomentCriticalNorm := by
  unfold zetaMomentCriticalNorm
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
  apply ContinuousAt.comp (g := riemannZeta)
    (f := fun u : ℝ => (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I))
  · exact (differentiableAt_riemannZeta hne).continuousAt
  · fun_prop


def pointValueSuperlevel (H V : ℝ) : Set ℝ :=
  {t | H ≤ t ∧ t ≤ 2*H ∧ V ≤ zetaMomentCriticalNorm t}

theorem isClosed_pointValueSuperlevel (H V : ℝ) :
    IsClosed (pointValueSuperlevel H V) := by
  have hs : IsClosed (Icc H (2*H) ∩ {t | V ≤ zetaMomentCriticalNorm t}) :=
    isClosed_Icc.inter
    (isClosed_le continuous_const continuous_zetaMomentCriticalNorm)
  convert hs using 1
  ext t
  simp only [pointValueSuperlevel,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_Icc]
  tauto

theorem measurableSet_pointValueSuperlevel (H V : ℝ) :
    MeasurableSet (pointValueSuperlevel H V) :=
  (isClosed_pointValueSuperlevel H V).measurableSet


theorem pointValueSuperlevel_subset_Icc (H V : ℝ) :
    pointValueSuperlevel H V ⊆ Icc H (2*H) :=
  fun _ ht => ⟨ht.1,ht.2.1⟩

theorem integrableOn_zeta_twelfth_pointValueSuperlevel (H V : ℝ) :
    IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (pointValueSuperlevel H V) :=
  ((continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc).mono_set
    (pointValueSuperlevel_subset_Icc H V)

theorem pointValue_power_tail_measure_le {H V s C : ℝ}
    (hV : 0 < V) (hs : 0 < s) (hC : 0 ≤ C)
    (hcount : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal (C/U^12)) :
    (volume.restrict (pointValueSuperlevel H V)).real
      {t | s ≤ zetaMomentCriticalNorm t^12} ≤ C/max (V^12) s := by
  have hevent : MeasurableSet {t | s ≤ zetaMomentCriticalNorm t^12} :=
    (isClosed_le continuous_const (continuous_zetaMomentCriticalNorm.pow 12)).measurableSet
  have hmeasure :
      (volume.restrict (pointValueSuperlevel H V))
        {t | s ≤ zetaMomentCriticalNorm t^12} ≤ ENNReal.ofReal (C/max (V^12) s) := by
    rw [Measure.restrict_apply hevent]
    by_cases hsmall : s ≤ V^12
    · rw [max_eq_left hsmall]
      exact (measure_mono inter_subset_right).trans (hcount V le_rfl)
    · have hVs : V^12 ≤ s := (lt_of_not_ge hsmall).le
      let U : ℝ := s^((12:ℝ)⁻¹)
      have hU : 0 < U := by dsimp only [U]; positivity
      have hUpow : U^12 = s := Real.rpow_inv_natCast_pow hs.le (by norm_num)
      have hVU : V ≤ U := le_of_pow_le_pow_left₀ (by norm_num : (12:ℕ) ≠ 0)
        hU.le (by simpa only [hUpow] using hVs)
      have hsub : {t | s ≤ zetaMomentCriticalNorm t^12} ∩
          pointValueSuperlevel H V ⊆ pointValueSuperlevel H U := by
        intro t ht
        refine ⟨ht.2.1,ht.2.2.1,?_⟩
        apply le_of_pow_le_pow_left₀ (by norm_num : (12:ℕ) ≠ 0)
          (show 0 ≤ zetaMomentCriticalNorm t from norm_nonneg _)
        simpa only [Set.mem_ofPred_eq, hUpow] using ht.1
      rw [max_eq_right hVs]
      exact (measure_mono hsub).trans (by simpa only [hUpow] using hcount U hVU)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal (div_nonneg hC ((pow_nonneg hV.le 12).trans (le_max_left _ _)))] at ht
  exact ht

theorem zeta_twelfth_high_integral_le_log {H V M C : ℝ}
    (hV : 0 < V) (hVM : V^12 ≤ M) (hC : 0 ≤ C)
    (hGrowth : ∀ t ∈ pointValueSuperlevel H V, zetaMomentCriticalNorm t^12 ≤ M)
    (hcount : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal (C/U^12)) :
    (∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) ≤
      C*(1+Real.log (M/V^12)) := by
  apply integral_le_log_of_truncated_tail (by positivity) hVM
    (integrableOn_zeta_twelfth_pointValueSuperlevel H V)
    (Filter.Eventually.of_forall (fun _ => by positivity))
  · filter_upwards [self_mem_ae_restrict (measurableSet_pointValueSuperlevel H V)] with t ht
    exact hGrowth t ht
  · intro s hs _
    exact pointValue_power_tail_measure_le hV hs hC hcount


theorem zeta_twelfth_low_integral_le_fourth (H V : ℝ) :
    (∫ t in Icc H (2*H) \ pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) ≤
      V^8*(∫ t in Icc H (2*H), zetaMomentCriticalNorm t^4) := by
  have h4 : IntegrableOn (fun t => zetaMomentCriticalNorm t^4) (Icc H (2*H)) :=
    (continuous_zetaMomentCriticalNorm.pow 4).continuousOn.integrableOn_Icc
  have h12 : IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (Icc H (2*H)) :=
    (continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc
  have hpoint : ∀ t ∈ Icc H (2*H) \ pointValueSuperlevel H V,
      zetaMomentCriticalNorm t^12 ≤ V^8*zetaMomentCriticalNorm t^4 := by
    intro t ht
    have hlt : zetaMomentCriticalNorm t < V := by
      by_contra hh
      exact ht.2 ⟨ht.1.1,ht.1.2,le_of_not_gt hh⟩
    have hp := pow_le_pow_left₀
      (show 0 ≤ zetaMomentCriticalNorm t from norm_nonneg _) hlt.le 8
    have hm := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ zetaMomentCriticalNorm t^4 by positivity)
    simpa only [← pow_add] using hm
  have hmeas : MeasurableSet (Icc H (2*H) \ pointValueSuperlevel H V) :=
    measurableSet_Icc.diff (measurableSet_pointValueSuperlevel H V)
  calc
    _ ≤ ∫ t in Icc H (2*H) \ pointValueSuperlevel H V,
        V^8*zetaMomentCriticalNorm t^4 :=
      setIntegral_mono_on (h12.mono_set sdiff_subset)
        ((h4.mono_set sdiff_subset).const_mul (V^8)) hmeas hpoint
    _ = V^8*(∫ t in Icc H (2*H) \ pointValueSuperlevel H V, zetaMomentCriticalNorm t^4) :=
      integral_const_mul _ _
    _ ≤ V^8*(∫ t in Icc H (2*H), zetaMomentCriticalNorm t^4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_set h4
        (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall sdiff_subset)

theorem zeta_twelfth_integral_le_high_add_fourth {H V : ℝ}
    (hH : 0 ≤ H) :
    (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤
      (∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) +
        V^8*(∫ t in H..2*H, zetaMomentCriticalNorm t^4) := by
  have h12 : IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (Icc H (2*H)) :=
    (continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc
  have he := setIntegral_sdiff (measurableSet_pointValueSuperlevel H V) h12
    (pointValueSuperlevel_subset_Icc H V)
  have hlow := zeta_twelfth_low_integral_le_fourth H V
  rw [he] at hlow
  rw [intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  linarith


end MathCollab.Density.Stronger
