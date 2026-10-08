module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.DensityTheorem

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MathCollab.Density
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

-- No growth, local-count, detector or family premise occurs in this type.
example : ∀ σ ε : ℝ, 3/4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ zetaZeroFinset σ (-T) T, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        C*T^(2*(1-σ)+ε) := by
  intro σ ε hσ hε
  obtain ⟨C,hC,h⟩ := zeta_density_bound hσ hε
  refine ⟨C,hC,?_⟩
  intro T hT
  simpa only [zetaDensityCount,zetaSlabCount,zetaMultiplicity,Nat.cast_sum] using h T hT

-- Literal region semantics: both ordinate signs, inclusive height and sigma edges.
example (σ T : ℝ) (ρ : ℂ) :
    ρ ∈ zetaZeroFinset σ (-T) T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
  rw [mem_zetaDensityFinset]
  simp only [IsNontrivialZetaZero, and_assoc]

-- The result covers the full stated range, including the empty range sigma>=1.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount 1 T : ℝ) ≤ C*T^ε := by
  simpa using zeta_density_bound (by norm_num : (3/4 : ℝ) < 1) hε

-- Multiplicity equality is an analytic-order equality, not a statement about
-- distinct ordinates or only cardinality of the zero set.
example {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) :
    analyticOrderNatAt riemannZeta (conj ρ) = analyticOrderNatAt riemannZeta ρ :=
  zetaMultiplicity_conj hρ

-- The fixed Weyl loss is independent of the counting loss.
example : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+1/96 : ℝ) :=
  actual_zeta_weyl_input (by norm_num)

-- The public counting allocation has the original strict 8eta and 12eta margins.
example {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    0 < min ((σ-3/4)/16) (ε/24) ∧
      8*min ((σ-3/4)/16) (ε/24) < σ-3/4 ∧
      12*min ((σ-3/4)/16) (ε/24) < ε :=
  densityCountingEta_margins hσ hε

-- In the stated range the strip predicate excludes no actual zeta zero.
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
