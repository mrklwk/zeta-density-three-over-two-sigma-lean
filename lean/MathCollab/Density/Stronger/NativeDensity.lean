module
-- Reversible module-visibility port of the audited development.
/-
Native stronger-density composition, preserving the original actual-zero count
and analytic multiplicities. Imported McColm proofs retain MIT-0 attribution;
Mathlib dependencies retain Apache-2.0 attribution.
See third_party/twelfth/NATIVE_ENDPOINTS_MANIFEST.json.
-/
public import MathCollab.Density.Stronger.NativeMoment
public import MathCollab.Density.DensityConclusion

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Filter MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Every actual nontrivial zeta zero with sigma<=Re(rho) and |Im(rho)|<=T is
counted with analytic multiplicity. The constant precedes all T>=2, and no
analytic producer premise remains. The sigma>=1 region has zero count. -/
theorem stronger_density_bound_native {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(3*(1-σ)/(2*σ)+ε) := by
  by_cases hσ' : σ < 1
  · exact stronger_density_bound_of_twelfth_moment hσ hσ' hε zeta_twelfth_physical_native
  · refine ⟨1, by norm_num, ?_⟩
    intro T hT
    rw [zetaDensityCount_eq_zero_of_one_le (not_lt.mp hσ')]
    simp only [Nat.cast_zero, one_mul]
    positivity

end MathCollab.Density.Stronger
