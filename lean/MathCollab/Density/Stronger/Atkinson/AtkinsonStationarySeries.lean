module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleSupport
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCarrierCoefficients
public import MathCollab.Density.Stronger.Fourth.Coefficients

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonStationaryLeadingIntegral (T G L : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt Real.pi/Real.pi : ℂ)*(atkinsonBesselScale (1/4) n : ℂ) *
    (neumannLeadingPlus*atkinsonStationaryMain T G L (1/4) (Real.sqrt n) +
      neumannLeadingMinus*atkinsonStationaryMain T G L (1/4) (-Real.sqrt n))

def atkinsonStationaryLeadingTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2*Real.pi) : ℂ) * atkinsonStationaryLeadingIntegral T G L n

def atkinsonStationaryLeadingFiniteSum (T G L : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonStationaryLeadingTerm T G L n

def atkinsonStationaryLeadingSum (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, atkinsonStationaryLeadingTerm T G L n

theorem atkinsonStationaryLeadingTerm_zero (T G L : ℝ) :
    atkinsonStationaryLeadingTerm T G L 0 = 0 := by
  simp [atkinsonStationaryLeadingTerm,divisorWeight]

theorem atkinsonStationaryLeadingTerm_eq_zero_after_cutoff {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G)
    {n : ℕ} (hn : atkinsonSourceCutoff T G L ≤ n) :
    atkinsonStationaryLeadingTerm T G L n = 0 := by
  obtain ⟨hp,hm⟩ := atkinsonStationaryMain_pair_eq_zero_after_cutoff hT hG hL hwidth (1/4) n hn
  simp only [atkinsonStationaryLeadingTerm,atkinsonStationaryLeadingIntegral,hp,hm,
    mul_zero,add_zero]

theorem hasSum_atkinsonStationaryLeadingTerm {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    HasSum (atkinsonStationaryLeadingTerm T G L)
      (atkinsonStationaryLeadingFiniteSum T G L (atkinsonSourceCutoff T G L)) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply atkinsonStationaryLeadingTerm_eq_zero_after_cutoff hT hG hL hwidth
  exact Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)

theorem atkinsonStationaryLeadingSum_eq_finite {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    atkinsonStationaryLeadingSum T G L =
      atkinsonStationaryLeadingFiniteSum T G L (atkinsonSourceCutoff T G L) :=
  (hasSum_atkinsonStationaryLeadingTerm hT hG hL hwidth).tsum_eq

end MathCollab.Density.Stronger.Atkinson
