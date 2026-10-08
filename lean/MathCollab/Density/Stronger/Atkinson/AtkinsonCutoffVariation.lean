module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorBandCutoff
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeBounds
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem intervalC1Bound_zetaBandCutoff {a b c d A B : ℝ}
    (hab : a < b) (hcd : c < d) (hAB : A ≤ B) :
    IntervalC1Bound (fun x => (zetaBandCutoff a b c d x : ℂ)) A B 2 := by
  let u : ℝ → ℝ := fun x => Real.smoothTransition ((x - a) / (b - a))
  let v : ℝ → ℝ := fun x => Real.smoothTransition ((d - x) / (d - c))
  have hu : Monotone u := Real.smoothTransition.monotone.comp
    (fun x y hxy => div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)
  have hv : Antitone v := Real.smoothTransition.monotone.comp_antitone
    (fun x y hxy => div_le_div_of_nonneg_right (sub_le_sub_left hxy d) (sub_pos.mpr hcd).le)
  have hsu : ContDiff ℝ 1 u := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hsv : ContDiff ℝ 1 v := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hbu := intervalC1Bound_ofReal_of_deriv_nonneg hAB (by norm_num : (0 : ℝ) ≤ 1)
    (fun x _ => hsu.contDiffAt (x := x))
    (fun x _ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
    (fun _ _ => hu.deriv_nonneg)
  have hbv := intervalC1Bound_ofReal_of_deriv_nonpos hAB (by norm_num : (0 : ℝ) ≤ 1)
    (fun x _ => hsv.contDiffAt (x := x))
    (fun x _ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
    (fun _ _ => hv.deriv_nonpos)
  simpa only [u, v, zetaBandCutoff, Complex.ofReal_mul, mul_one] using hbu.mul hbv hAB

theorem intervalC1Bound_zetaDivisorBandCutoff {T G L A B : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hAB : A ≤ B) :
    IntervalC1Bound (fun x => (zetaDivisorBandCutoff T G L x : ℂ)) A B 2 := by
  have hm := zetaDivisorBandEdge_strictMono hT hG
  exact intervalC1Bound_zetaBandCutoff (hm (by linarith)) (hm (by linarith)) hAB

theorem finiteVariationBound_zetaBandCutoff_sample {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (u : ℕ → ℝ) (N : ℕ)
    (hu : MonotoneOn u (Iic N) ∨ AntitoneOn u (Iic N)) :
    FiniteVariationBound (fun i => (zetaBandCutoff a b c d (u i) : ℂ)) N 2 := by
  let p : ℝ → ℝ := fun x => Real.smoothTransition ((x-a)/(b-a))
  let q : ℝ → ℝ := fun x => Real.smoothTransition ((d-x)/(d-c))
  have hp : Monotone p := fun x y hxy =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)
  have hq : Antitone q := fun x y hxy =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_left hxy d) (sub_pos.mpr hcd).le)
  have hbnd (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
      (hm : Monotone f ∨ Antitone f) :
      FiniteVariationBound (fun i => (f (u i) : ℂ)) N 1 := by
    rcases hm with hm | hm <;> rcases hu with hu | hu
    · exact finiteVariationBound_of_monotone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
    · exact finiteVariationBound_of_antitone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
    · exact finiteVariationBound_of_antitone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
    · exact finiteVariationBound_of_monotone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
  have h₁ := hbnd p (fun _ => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩) (Or.inl hp)
  have h₂ := hbnd q (fun _ => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩) (Or.inr hq)
  simpa only [p,q,zetaBandCutoff,Complex.ofReal_mul,mul_one] using h₁.mul h₂

end MathCollab.Density.Stronger.Atkinson
