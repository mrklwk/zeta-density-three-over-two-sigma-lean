module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SeparatedMoment
public import MathCollab.Density.Stronger.WeightedCriticalMean
public import MathCollab.Density.Stronger.CriticalMoment

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem zetaMomentCriticalNorm_nonneg (t : ℝ) : 0 ≤ zetaMomentCriticalNorm t := norm_nonneg _

theorem zetaMomentCriticalNorm_le_linear (t : ℝ) :
    zetaMomentCriticalNorm t ≤ 4*(1+|t|) := by
  simpa only [zetaMomentCriticalNorm, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    norm_riemannZeta_critical_le_linear t

def weightedCriticalTwelfth (A : ℕ) (γ : ℝ) : ℝ :=
  ∫ t : ℝ, momentDecay A t*zetaMomentCriticalNorm (γ+t)^12

/-- Absolute convergence follows from coarse actual-zeta growth alone. -/
theorem integrable_weightedCriticalTwelfth (A : ℕ) (hA : 14 ≤ A) (γ : ℝ) :
    Integrable (fun t : ℝ => momentDecay A t*zetaMomentCriticalNorm (γ+t)^12) := by
  have hc : Continuous (fun t : ℝ => momentDecay A t*zetaMomentCriticalNorm (γ+t)^12) :=
    (momentDecay_continuous A).mul
      (((continuous_zetaMomentCriticalNorm).comp (by fun_prop)).pow 12)
  have hmajor : Integrable (fun t : ℝ => (4*(1+|γ|))^12*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply hmajor.mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  rw [Real.norm_of_nonneg (mul_nonneg (momentDecay_pos A t).le (by positivity))]
  have hz : zetaMomentCriticalNorm (γ+t) ≤ 4*(1+|γ|)*(1+|t|) := by
    have h := zetaMomentCriticalNorm_le_linear (γ+t)
    have hab := abs_add_le γ t
    nlinarith [mul_nonneg (abs_nonneg γ) (abs_nonneg t)]
  have hp : (1+|t|)^14 ≤ (1+|t|)^A :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hA
  calc
    _ = zetaMomentCriticalNorm (γ+t)^12/(1+|t|)^A := by unfold momentDecay; ring
    _ ≤ (4*(1+|γ|)*(1+|t|))^12/(1+|t|)^14 :=
      div_le_div₀ (by positivity)
        (pow_le_pow_left₀ (zetaMomentCriticalNorm_nonneg _) hz 12) (by positivity) hp
    _ = (4*(1+|γ|))^12/(1+|t|)^2 := by
      rw [mul_pow]
      field_simp
    _ ≤ (4*(1+|γ|))^12*(1+t^2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_abs t, abs_nonneg t]

/-- Holder is applied to the actual critical-line mean, with every
integrability premise discharged. It does not assume a moment bound. -/
theorem weightedCriticalMean_twelfth_le {A : ℕ} (hA : 14 ≤ A) (γ : ℝ) :
    (weightedCriticalMean A γ)^12 ≤ Real.pi^11*weightedCriticalTwelfth A γ := by
  have hi : Integrable (fun t : ℝ => momentDecay A t*zetaMomentCriticalNorm (γ+t)) := by
    simpa [momentDecay, zetaMomentCriticalNorm, div_eq_mul_inv, mul_comm] using
      integrable_weightedCriticalMean A (by omega) γ
  have h := momentDecay_holder_twelfth (by omega : 2 ≤ A)
    (fun t => zetaMomentCriticalNorm_nonneg (γ+t)) hi (integrable_weightedCriticalTwelfth A hA γ)
  simpa [weightedCriticalMean, weightedCriticalTwelfth, momentDecay,
    zetaMomentCriticalNorm, div_eq_mul_inv, mul_comm] using h

/-- Exact translation from local offsets to the physical ordinate. -/
theorem weightedCriticalTwelfth_eq_translated (A : ℕ) (γ : ℝ) :
    weightedCriticalTwelfth A γ =
      ∫ t : ℝ, momentDecay A (t-γ)*zetaMomentCriticalNorm t^12 := by
  have h := integral_add_left_eq_self (μ := volume)
    (fun t : ℝ => momentDecay A (t-γ)*zetaMomentCriticalNorm t^12) γ
  simpa only [weightedCriticalTwelfth, add_sub_cancel_left] using h

/-- Separated translates restricted to a physical interval cost no factor
counting the number of zeros. The local twelfth moment is still literal. -/
theorem separated_critical_twelfth_on_interval {A : ℕ} (hA : 2 ≤ A)
    {U : Finset ℝ} (hU : oneSeparated U) (a b : ℝ) :
    (∑ u ∈ U, ∫ t in Icc a b, momentDecay A (t-u)*zetaMomentCriticalNorm t^12) ≤
      separationMass * ∫ t in Icc a b, zetaMomentCriticalNorm t^12 := by
  apply separated_momentDecay_integral_le
    ((continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc)
    (fun t => pow_nonneg (zetaMomentCriticalNorm_nonneg t) 12) hA hU

end MathCollab.Density.Stronger
