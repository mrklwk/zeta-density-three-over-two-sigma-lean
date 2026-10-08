module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.LongMultiplicityReduction
public import MathCollab.Density.Stronger.LongScalarBudget
public import MathCollab.Density.Stronger.FinalParameters
public import MathCollab.Density.DensityDyadicSummation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Filter MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Conditional on the displayed literal twelfth moment, the actual long
subset, including analytic multiplicities, retains an exponent saving. -/
theorem smoothLongZeroCount_bound_of_twelfth_moment {σ δ η ν D : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1/8)
    (hδm : δ < (1-smoothingExponent σ)/12) (hη : 0 < η)
    (hν : 0 ≤ ν) (hν' : ν ≤ (1-smoothingExponent σ)/8) (hD : 0 ≤ D)
    (hmoment : ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ D*T^(2+ν)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (smoothLongZeroCount η σ δ T : ℝ) ≤
        K*T^(densityExponent σ-(1-smoothingExponent σ)/4) := by
  obtain ⟨C,hC,hraw⟩ := smoothLongZeroCount_physical_moment_reduction hσ hσ' hδ hδ' hη
  refine ⟨C*(D+1),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),hraw,hmoment,
    long_count_scalar_log_eventually 13 hσ hδm hν'] with T hT hrawT hmomentT hscalar
  have hTp : 0 < T := by linarith
  have hXp : 0 ≤ detectorX δ T := Real.rpow_nonneg hTp.le _
  have hYp : 0 < detectorY σ T := Real.rpow_pos_of_pos hTp _
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have htail : T^(-113 : ℝ) ≤ T^(2+ν) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hbracket : (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12)+T^(-113 : ℝ) ≤
      (D+1)*T^(2+ν) := by nlinarith
  have hpre : (smoothLongZeroCount η σ δ T : ℝ)*(detectorY σ T)^(6*σ-3) ≤
      (C*(D+1))*((detectorX δ T)^6*(Real.log T)^13*T^(2+ν)) := by
    apply hrawT.trans
    calc
      _ ≤ C*(detectorX δ T)^6*(Real.log T)^13*((D+1)*T^(2+ν)) :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ = _ := by ring
  have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hYp (6*σ-3))).mpr hpre
  calc
    _ ≤ (C*(D+1))*((detectorX δ T)^6*(Real.log T)^13*T^(2+ν)/(detectorY σ T)^(6*σ-3)) := by
      simpa only [mul_div_assoc] using hdiv
    _ ≤ _ := mul_le_mul_of_nonneg_left hscalar (by positivity)

/-- All original positive-slab zeros are counted, conditionally only on the
literal actual-zeta twelfth moment displayed below. -/
theorem stronger_slab_bound_of_twelfth_moment {σ δ η ν D : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1/8)
    (hδm : δ < (1-smoothingExponent σ)/12) (hη : 0 < η)
    (hmargin : 8*η < σ-3/4) (hν : 0 ≤ ν) (hν' : ν ≤ (1-smoothingExponent σ)/8)
    (hD : 0 ≤ D)
    (hmoment : ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ D*T^(2+ν)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (zetaSlabCount σ T (2*T) : ℝ) ≤ C*T^(densityExponent σ+12*η) := by
  obtain ⟨Cs,hCs,hs⟩ := smoothShortZeroCount_bound hσ hσ' hη hmargin δ
  obtain ⟨Cl,hCl,hl⟩ := smoothLongZeroCount_bound_of_twelfth_moment
    hσ hσ' hδ hδ' hδm hη hν hν' hD hmoment
  refine ⟨Cs+Cl,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),hs,hl] with T hT hsT hlT
  have hp : T^(densityExponent σ-(1-smoothingExponent σ)/4) ≤
      T^(densityExponent σ+12*η) :=
    Real.rpow_le_rpow_of_exponent_le hT (by have := smoothingExponent_lt_one hσ; linarith)
  have hl' := hlT.trans (mul_le_mul_of_nonneg_left hp hCl.le)
  rw [smooth_zeroCount_partition η σ δ T, Nat.cast_add]
  nlinarith

/-- Conditional final interface. The twelfth-moment estimate is an explicit
analytic hypothesis, not a theorem proved or assumed by this module. Every
other detector, family, counting, multiplicity and height-summation input is
supplied by verified production lemmas. -/
theorem stronger_density_bound_of_twelfth_moment {σ ε : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hε : 0 < ε)
    (hmoment : ∀ ν : ℝ, 0 < ν → ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ D*T^(2+ν)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(3*(1-σ)/(2*σ)+ε) := by
  obtain ⟨δ,η,ν,hδ,hδ',hδm,hη,hmargin,hηε,hν,hν'⟩ := exists_stronger_loss_parameters hσ hε
  obtain ⟨D,hD,hm⟩ := hmoment ν hν
  obtain ⟨C,hC,hslab⟩ := stronger_slab_bound_of_twelfth_moment
    hσ hσ' hδ hδ' hδm hη hmargin hν.le hν' hD.le hm
  have hp : 0 < densityExponent σ+12*η := by
    have := densityExponent_pos hσ hσ'
    linarith
  obtain ⟨B,hB,hbound⟩ := zetaDensity_bound_of_eventual_slabs hp hC hslab
  refine ⟨B,hB,?_⟩
  intro T hT
  apply (hbound T hT).trans
  apply mul_le_mul_of_nonneg_left _ hB.le
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
  change densityExponent σ+12*η ≤ densityExponent σ+ε
  linarith

end MathCollab.Density.Stronger
