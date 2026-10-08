module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonResidualVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonGaussianVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCoefficientVariation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonPositiveMainWeight (T G L : ℝ) (n : ℕ) : ℂ :=
  (atkinsonFourthRootCoefficient T n : ℂ) * atkinsonSaddleGaussian T G n *
    atkinsonSaddleResidual T G L (Real.sqrt n)

def atkinsonNegativeMainWeight (T G L : ℝ) (n : ℕ) : ℂ :=
  (atkinsonFourthRootCoefficient T n : ℂ) * atkinsonSaddleGaussian T G n *
    atkinsonSaddleResidual T G L (-Real.sqrt n)

theorem exists_finiteVariationBound_atkinsonMainWeights :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T → 0 < L →
      ∀ m N : ℕ, 0 < m → 10000*((m+N:ℕ):ℝ) ≤ T →
      FiniteVariationBound (fun i => atkinsonPositiveMainWeight T G L (m+i)) N
        (C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))) ∧
      FiniteVariationBound (fun i => atkinsonNegativeMainWeight T G L (m+i)) N
        (C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))) := by
  obtain ⟨D,hD,hres⟩ := exists_finiteVariationBound_saddleResidual
  let K : ℝ := (1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨8*K*Real.sqrt Real.pi*D,by positivity,?_⟩
  intro T G L hT hG hGT hL m N hm hN
  have hmT : (m:ℝ) ≤ T := by
    have hcast : (m:ℝ) ≤ (m+N:ℕ) := by exact_mod_cast Nat.le_add_right m N
    have hn0 : (0:ℝ) ≤ (m+N:ℕ) := Nat.cast_nonneg _
    linarith
  have hc := finiteVariationBound_fourthRootCoefficient hT hm N
  have hg := finiteVariationBound_atkinsonSaddleGaussian_physical hT hG hGT m N hmT
  obtain ⟨hrp,hrm⟩ := hres T G L hT hG hL m N hN
  constructor
  · convert (hc.mul hg).mul hrp using 1
    · rfl
    · dsimp [K]
      ring
  · convert (hc.mul hg).mul hrm using 1
    · rfl
    · dsimp [K]
      ring

end MathCollab.Density.Stronger.Atkinson
