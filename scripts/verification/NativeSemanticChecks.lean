module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.NativeDensity

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MathCollab.Density MathCollab.Density.Stronger MeasureTheory Filter Set
open scoped BigOperators
set_option autoImplicit false

-- No source, packet, point-mean, peak, growth, or moment premise occurs here.
example : ∀ σ ε : ℝ, 3/4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ zetaZeroFinset σ (-T) T, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        C*T^(3*(1-σ)/(2*σ)+ε) := by
  intro σ ε hσ hε
  obtain ⟨C,hC,h⟩ := stronger_density_bound_native hσ hε
  refine ⟨C,hC,?_⟩
  intro T hT
  simpa only [zetaDensityCount,zetaSlabCount,zetaMultiplicity,Nat.cast_sum] using h T hT

-- The physical twelfth moment uses the actual mathlib riemannZeta and norm.
example : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
    (∫ t in Icc 0 (3*T), ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖^12) ≤ K*T^(2+ε) := by
  simpa only [zetaMomentCriticalNorm, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using zeta_twelfth_physical_native

-- The dyadic counterpart has the same literal integrand.
example : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ H : ℝ in atTop,
    (∫ t in H..2*H, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖^12) ≤ D*H^(2+ε) := by
  simpa only [zetaMomentCriticalNorm, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using zeta_twelfth_dyadic_native

-- The peak set concerns actual point values at their original physical heights.
example : ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
    0 < V → H^(1/8+η) ≤ V → ∀ W : Finset ℝ,
    oneSeparated W →
    (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ V ≤ ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖) →
    (W.card : ℝ)*V^12 ≤ H^(2+η) := by
  simpa only [pointValueSuperlevel, Set.mem_ofPred_eq, zetaMomentCriticalNorm,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using pointValue_peak_card_native

-- Inclusive real-part and symmetric height cutoffs omit no actual zero in range.
example {σ : ℝ} (hσ : 3/4 < σ) (T : ℝ) (ρ : ℂ) :
    ρ ∈ zetaZeroFinset σ (-T) T ↔
      riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
  rw [mem_zetaDensityFinset]
  constructor
  · rintro ⟨hz,hre,hheight⟩
    exact ⟨hz.1,hre,hheight⟩
  · rintro ⟨hz,hre,hheight⟩
    have hupper : ρ.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
    exact ⟨⟨hz,by linarith,hupper⟩,hre,hheight⟩

-- The stated sigma range also includes the empty region at sigma=1.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount 1 T : ℝ) ≤ C*T^ε := by
  simpa using stronger_density_bound_native (by norm_num : (3/4 : ℝ) < 1) hε
