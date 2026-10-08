module
-- Reversible module-visibility port of the audited development.
/-
Native composition of the verified point-mean and actual stationary-source producers.
The narrowly ported analytic inputs retain McColm's MIT-0 attribution;
Mathlib and other imported foundations retain their Apache-2.0 attribution.
See third_party/twelfth/NATIVE_ENDPOINTS_MANIFEST.json.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNativeLocalMean
public import MathCollab.Density.Stronger.PointMean.PeaksInput
public import MathCollab.Density.Stronger.Peaks.WidthRanges
public import MathCollab.Density.Stronger.MomentFromPeaks

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Filter MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Every finite one-separated set of actual high zeta values obeys the native
weighted twelfth-power count. The threshold precedes the height and finite set. -/
theorem pointValue_peak_card_native :
    ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V → ∀ W : Finset ℝ,
      oneSeparated W → (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η) :=
  Peaks.pointValue_peak_card_of_inputs PointMean.pointMeanInput_native
    (Atkinson.localMeanPacketInput_of_stationary Atkinson.localMeanStationaryInput_native)

/-- Lebesgue measure of the literal actual-zeta high-value set. -/
theorem pointValue_volume_native :
    ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+η)/V^12) := by
  intro η hη
  filter_upwards [pointValue_peak_card_native η hη] with H hH
  intro V hV hVH
  exact pointValue_volume_le_of_peak_card hV (hH V hV hVH)

end MathCollab.Density.Stronger
