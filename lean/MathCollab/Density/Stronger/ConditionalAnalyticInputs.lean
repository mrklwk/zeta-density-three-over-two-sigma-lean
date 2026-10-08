module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.Peaks.WidthRanges
public import MathCollab.Density.Stronger.MomentFromPeaks

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Filter MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Conditional analytic interface. Both native producers are explicit
parameters with literal zeta definitions in Peaks.Inputs. Neither is supplied
or postulated by this declaration. -/
theorem zeta_twelfth_physical_of_analytic_inputs
    (hPointMean : Peaks.PointMeanInput) (hPacket : Peaks.LocalMeanPacketInput) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε) := by
  exact zeta_twelfth_physical_of_peak_card
    (Peaks.pointValue_peak_card_of_inputs hPointMean hPacket)

/-- The stronger density conclusion from exactly the two explicitly displayed
native analytic producers; NativeDensity supplies both producers and proves the unconditional endpoint. -/
theorem stronger_density_bound_of_analytic_inputs {σ ε : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hε : 0 < ε)
    (hPointMean : Peaks.PointMeanInput) (hPacket : Peaks.LocalMeanPacketInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(3*(1-σ)/(2*σ)+ε) := by
  exact stronger_density_bound_of_twelfth_moment hσ hσ' hε
    (zeta_twelfth_physical_of_analytic_inputs hPointMean hPacket)

end MathCollab.Density.Stronger
