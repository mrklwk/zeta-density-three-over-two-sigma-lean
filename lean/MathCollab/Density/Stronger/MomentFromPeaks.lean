module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.ConditionalMoment
public import MathCollab.Density.Stronger.SeparatedVolume
public import MathCollab.Density.Stronger.Fourth.FourthMoment
public import MathCollab.Density.Stronger.ConditionalDensity

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Filter Set
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The literal fourth moment is now supplied by a proved producer. -/
theorem actual_fourth_moment_eventually (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η) := by
  obtain ⟨C,B,hC,hfourth⟩ := Fourth.zeta_fourth_dyadic η hη
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop B,eventually_gt_atTop (0 : ℝ)] with H hH hH0
  exact hfourth H hH hH0

/-- Generic separated covering applied to the literal actual-zeta superlevel.
The actual finite-peak bound remains the displayed hypothesis. -/
theorem pointValue_volume_le_of_peak_card {H V η : ℝ} (hV : 0 < V)
    (hpeaks : ∀ W : Finset ℝ, oneSeparated W →
      (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η)) :
    volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+η)/V^12) := by
  have hc : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      oneSeparated W → (W.card : ℝ) ≤ H^(2+η)/V^12 := by
    intro W hW hsep
    exact (le_div_iff₀ (pow_pos hV 12)).mpr (hpeaks W hsep hW)
  have h := volume_le_two_mul_of_separated_card_bound hc
  simpa only [mul_div_assoc] using h

/-- Fourth moment and all growth are discharged. The actual high-value finite
peak count is the only remaining analytic input of this moment consumer. -/
theorem zeta_twelfth_physical_of_peak_card
    (hpeaks : ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V → ∀ W : Finset ℝ,
      oneSeparated W → (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε) := by
  apply zeta_twelfth_physical_of_fourth_and_tail actual_fourth_moment_eventually
  intro η hη
  filter_upwards [hpeaks η hη] with H hH
  intro V hV hVH
  exact pointValue_volume_le_of_peak_card hV (hH V hV hVH)

/-- A second explicit conditional endpoint, isolating the remaining actual
high-value finite-peak producer. This does not prove that producer. -/
theorem stronger_density_bound_of_peak_card {σ ε : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hε : 0 < ε)
    (hpeaks : ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V → ∀ W : Finset ℝ,
      oneSeparated W → (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(3*(1-σ)/(2*σ)+ε) := by
  exact stronger_density_bound_of_twelfth_moment hσ hσ' hε
    (zeta_twelfth_physical_of_peak_card hpeaks)

end MathCollab.Density.Stronger
