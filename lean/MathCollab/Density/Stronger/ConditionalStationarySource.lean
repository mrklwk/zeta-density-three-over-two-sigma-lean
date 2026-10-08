module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.ConditionalAnalyticInputs
public import MathCollab.Density.Stronger.PointMean.PeaksInput
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSourceAssembly

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Filter MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The actual peak count from the remaining pointwise stationary source
inequality. Native point-mean and physical packet estimates are supplied by
their proved producers. The source inequality stays an explicit parameter. -/
theorem pointValue_peak_card_of_stationary_source
    (hSource : Atkinson.LocalMeanSourceToPrefix) :
    ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V → ∀ W : Finset ℝ,
      oneSeparated W → (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η) := by
  exact Peaks.pointValue_peak_card_of_inputs PointMean.pointMeanInput_native
    (Atkinson.localMeanPacketInput_of_sourceToPrefix hSource)

/-- Literal physical twelfth-moment conclusion, conditional only on the
displayed stationary source inequality for the actual local second moment. -/
theorem zeta_twelfth_physical_of_stationary_source
    (hSource : Atkinson.LocalMeanSourceToPrefix) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε) := by
  exact zeta_twelfth_physical_of_analytic_inputs PointMean.pointMeanInput_native
    (Atkinson.localMeanPacketInput_of_sourceToPrefix hSource)

/-- Complete stronger density reduction with one remaining literal analytic
source premise. This declaration does not supply that premise. -/
theorem stronger_density_bound_of_stationary_source {σ ε : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hε : 0 < ε)
    (hSource : Atkinson.LocalMeanSourceToPrefix) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(3*(1-σ)/(2*σ)+ε) := by
  exact stronger_density_bound_of_analytic_inputs hσ hσ' hε
    PointMean.pointMeanInput_native
    (Atkinson.localMeanPacketInput_of_sourceToPrefix hSource)

end MathCollab.Density.Stronger
