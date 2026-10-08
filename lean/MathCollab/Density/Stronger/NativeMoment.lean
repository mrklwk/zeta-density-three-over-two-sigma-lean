module
-- Reversible module-visibility port of the audited development.
/-
Native actual-zeta moment composition. The narrowly ported analytic inputs retain
McColm's MIT-0 attribution; Mathlib dependencies retain Apache-2.0 attribution.
See third_party/twelfth/NATIVE_ENDPOINTS_MANIFEST.json.
-/
public import MathCollab.Density.Stronger.NativePeaks

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Filter MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The actual critical-line twelfth moment on every sufficiently high dyadic
interval, with one constant before all heights. -/
theorem zeta_twelfth_dyadic_native :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε) :=
  zeta_twelfth_dyadic_of_fourth_and_tail actual_fourth_moment_eventually
    pointValue_volume_native

/-- The complete literal physical twelfth moment. Both actual fourth moment
and actual high-value tail are supplied by proved native producers. -/
theorem zeta_twelfth_physical_native :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε) := by
  intro ε hε
  obtain ⟨D, hD, hdyadic⟩ := zeta_twelfth_dyadic_native ε hε
  exact zeta_twelfth_physical_of_dyadic hε hD.le hdyadic

end MathCollab.Density.Stronger
