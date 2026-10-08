module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- Gaussian integrability with an arbitrary natural absolute-value moment. -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq
    {b : ℝ} (hb : 0 < b) (j : ℕ) :
    Integrable (fun u : ℝ => |u| ^ j * Real.exp (-b * u ^ 2)) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have hpos : IntegrableOn
      (fun u : ℝ => |u| ^ j * Real.exp (-b * u ^ 2)) (Set.Ioi 0) := by
    have hraw := integrableOn_rpow_mul_exp_neg_mul_sq hb
      (s := (j : ℝ)) (by
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith)
    apply hraw.congr_fun _ measurableSet_Ioi
    intro u hu
    dsimp only
    rw [Real.rpow_natCast, abs_of_pos (Set.mem_Ioi.mp hu)]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_zero]
    using hpos

theorem integrable_exp_sub_mul_sq_mul_add_abs_pow
    (A : ℝ) {B C : ℝ} (hB : 0 < B) (j : ℕ) :
    Integrable (fun u : ℝ =>
      Real.exp (A - B * u ^ 2) * (C + |u|) ^ j) := by
  have hterm : ∀ i ∈ Finset.range (j + 1), Integrable (fun u : ℝ =>
      (Real.exp A * (j.choose i : ℝ) * C ^ i) *
        (|u| ^ (j - i) * Real.exp (-B * u ^ 2))) := by
    intro i _hi
    exact (integrable_abs_pow_mul_exp_neg_mul_sq hB (j - i)).const_mul
      (Real.exp A * (j.choose i : ℝ) * C ^ i)
  have hsum : Integrable (fun u : ℝ =>
      ∑ i ∈ Finset.range (j + 1),
        (Real.exp A * (j.choose i : ℝ) * C ^ i) *
          (|u| ^ (j - i) * Real.exp (-B * u ^ 2))) :=
    integrable_finsetSum (Finset.range (j + 1)) hterm
  apply hsum.congr
  filter_upwards with u
  rw [sub_eq_add_neg, Real.exp_add, add_pow]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring_nf

end MathCollab.Density.Stronger.Atkinson
