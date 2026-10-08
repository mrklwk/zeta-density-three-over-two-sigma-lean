module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.NativeDensity

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex MathCollab.Density MathCollab.Density.Stronger MeasureTheory Filter Set
open scoped BigOperators
set_option autoImplicit false
namespace DensityStronger

theorem exact_membership {σ : ℝ} (hσ : 3/4 < σ) (T : ℝ) (ρ : ℂ) :
    ρ ∈ zetaZeroFinset σ (-T) T ↔
      riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
  rw [mem_zetaDensityFinset]
  constructor
  · rintro ⟨hz, hr, hi⟩
    exact ⟨hz.1, hr, hi⟩
  · rintro ⟨hz, hr, hi⟩
    have hu : ρ.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
    exact ⟨⟨hz, by linarith, hu⟩, hr, hi⟩

theorem exact_multiplicity {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroFinset σ (-T) T) :
    0 < analyticOrderNatAt riemannZeta ρ ∧
    (analyticOrderNatAt riemannZeta ρ : ℕ∞) = analyticOrderAt riemannZeta ρ ∧
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  have hz := (mem_zetaZeroFinset.mp hρ).1
  exact ⟨zetaMultiplicity_pos hz, zetaMultiplicity_cast (nontrivialZetaZero_ne_one hz),
    zeta_analyticOrder_ne_top (nontrivialZetaZero_ne_one hz)⟩

-- Only the actual zero predicate and analytic order occur in this conclusion.
theorem density_bound : ∀ σ ε : ℝ, 3/4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
        (∀ ρ ∈ Z, 0 < analyticOrderNatAt riemannZeta ρ ∧
          (analyticOrderNatAt riemannZeta ρ : ℕ∞) = analyticOrderAt riemannZeta ρ ∧
          analyticOrderAt riemannZeta ρ ≠ ⊤) ∧
        (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
          C*T^(3*(1-σ)/(2*σ)+ε) := by
  intro σ ε hσ hε
  obtain ⟨C, hC, hb⟩ := stronger_density_bound_native hσ hε
  refine ⟨C, hC, ?_⟩
  intro T hT
  refine ⟨zetaZeroFinset σ (-T) T, exact_membership hσ T, ?_, ?_⟩
  · exact fun ρ hρ => exact_multiplicity hρ
  · simpa only [zetaDensityCount, zetaSlabCount, zetaMultiplicity, Nat.cast_sum] using hb T hT

-- The integral is genuinely integrable for every finite interval, not merely
-- the totalized value of a nonintegrable function.
theorem actual_moment_integrable (a b : ℝ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖^n) (Icc a b) := by
  have hi : IntegrableOn (fun t : ℝ => zetaMomentCriticalNorm t ^ n) (Icc a b) volume :=
    (continuous_zetaMomentCriticalNorm.pow n).continuousOn.integrableOn_Icc
  simpa only [zetaMomentCriticalNorm, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using hi

theorem twelfth_moment : ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ t in Icc 0 (3*T), ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖^12) ≤
        K*T^(2+ε) := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := zeta_twelfth_physical_native ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hb
  refine ⟨K, hK, T₀, ?_⟩
  simpa only [zetaMomentCriticalNorm, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using hT₀

theorem empty_region {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) :
    zetaDensityCount σ T = 0 := zetaDensityCount_eq_zero_of_one_le hσ T

end DensityStronger
