module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.Parameters

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Filter
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- All scalar loss choices precede the height and the zero. This statement
supplies no analytic moment estimate. -/
theorem exists_stronger_loss_parameters {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    ∃ δ η ν : ℝ, 0 < δ ∧ δ ≤ 1/8 ∧ δ < (1-smoothingExponent σ)/12 ∧
      0 < η ∧ 8*η < σ-3/4 ∧ 12*η ≤ ε ∧
      0 < ν ∧ ν ≤ (1-smoothingExponent σ)/8 := by
  obtain ⟨δ,hδ,hδ',hδ''⟩ := exists_detector_exponent hσ
  let η : ℝ := min (ε/24) ((σ-3/4)/16)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηa : η ≤ ε/24 := min_le_left _ _
  have hηb : η ≤ (σ-3/4)/16 := min_le_right _ _
  have hc := smoothingExponent_lt_one hσ
  refine ⟨δ,η,(1-smoothingExponent σ)/16,hδ,hδ'.le,hδ'',hη,?_,?_,?_,?_⟩ <;> linarith

end MathCollab.Density.Stronger
