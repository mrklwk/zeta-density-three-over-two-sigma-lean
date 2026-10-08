module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Packing
public import MathCollab.Density.Stronger.MomentPower
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The fixed nonnegative weight used for separated moment sampling. -/
def momentDecay (A : ℕ) (t : ℝ) : ℝ := 1/(1+|t|)^A

theorem momentDecay_pos (A : ℕ) (t : ℝ) : 0 < momentDecay A t := by
  unfold momentDecay
  positivity

theorem momentDecay_le_one (A : ℕ) (t : ℝ) : momentDecay A t ≤ 1 := by
  unfold momentDecay
  apply (div_le_one (by positivity)).mpr
  exact one_le_pow₀ (by linarith [abs_nonneg t])

theorem momentDecay_antitone {A B : ℕ} (hAB : A ≤ B) (t : ℝ) :
    momentDecay B t ≤ momentDecay A t := by
  unfold momentDecay
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_right₀ (by linarith [abs_nonneg t]) hAB

theorem momentDecay_continuous (A : ℕ) : Continuous (momentDecay A) := by
  unfold momentDecay
  apply continuous_const.div
  · fun_prop
  · intro t; positivity

theorem momentDecay_le_inv_one_add_sq {A : ℕ} (hA : 2 ≤ A) (t : ℝ) :
    momentDecay A t ≤ (1+t^2)⁻¹ := by
  apply (momentDecay_antitone hA t).trans
  unfold momentDecay
  rw [← one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [sq_abs t, abs_nonneg t]

theorem integrable_momentDecay {A : ℕ} (hA : 2 ≤ A) : Integrable (momentDecay A) := by
  refine integrable_inv_one_add_sq.mono' (momentDecay_continuous A).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro t
  rw [Real.norm_of_nonneg (momentDecay_pos A t).le]
  exact momentDecay_le_inv_one_add_sq hA t

theorem momentDecay_mass_bounds {A : ℕ} (hA : 2 ≤ A) :
    0 < ∫ t : ℝ, momentDecay A t ∧ (∫ t : ℝ, momentDecay A t) ≤ Real.pi := by
  constructor
  · apply (integral_pos_iff_support_of_nonneg (fun t => (momentDecay_pos A t).le)
      (integrable_momentDecay hA)).mpr
    have he : Function.support (momentDecay A) = univ := by
      ext t
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (momentDecay_pos A t).ne'
    rw [he]
    simp
  · calc
      _ ≤ ∫ t : ℝ, (1+t^2)⁻¹ := integral_mono (integrable_momentDecay hA)
        integrable_inv_one_add_sq (momentDecay_le_inv_one_add_sq hA)
      _ = Real.pi := integral_univ_inv_one_add_sq

/-- Weighted Holder with a fixed absolute mass bound; analytic inputs are the
explicit integrability hypotheses, not a zeta moment estimate. -/
theorem momentDecay_holder_twelfth {A : ℕ} (hA : 2 ≤ A) {f : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ f t)
    (hi : Integrable (fun t => momentDecay A t*f t))
    (hi12 : Integrable (fun t => momentDecay A t*f t^12)) :
    (∫ t : ℝ, momentDecay A t*f t)^12 ≤
      Real.pi^11 * ∫ t : ℝ, momentDecay A t*f t^12 := by
  have hm := momentDecay_mass_bounds hA
  apply (integral_weighted_twelfth (fun t => (momentDecay_pos A t).le) hf
    (integrable_momentDecay hA) hi hi12 hm.1).trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm.1.le hm.2 11)
    (integral_nonneg (fun t => mul_nonneg (momentDecay_pos A t).le (pow_nonneg (hf t) 12)))

/-- One common sampling constant for every separated set and every translate. -/
theorem separated_momentDecay_row {A : ℕ} (hA : 2 ≤ A) {U : Finset ℝ}
    (hU : oneSeparated U) (t : ℝ) :
    (∑ u ∈ U, momentDecay A (t-u)) ≤ separationMass := by
  calc
    _ ≤ ∑ u ∈ U, momentDecay 2 (t-u) :=
      Finset.sum_le_sum (fun u _ => momentDecay_antitone hA (t-u))
    _ ≤ _ := separated_decay_row hU t

theorem integrable_momentDecay_mul {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f μ) (A : ℕ) (u : ℝ) :
    Integrable (fun t => momentDecay A (t-u)*f t) μ := by
  have hc : Continuous (fun t => momentDecay A (t-u)) :=
    (momentDecay_continuous A).comp (by fun_prop)
  apply hf.norm.mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  change ‖momentDecay A (t-u)*f t‖ ≤ ‖f t‖
  rw [norm_mul, Real.norm_of_nonneg (momentDecay_pos A (t-u)).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (momentDecay_le_one _ _)

/-- Finite separated translates cost an absolute constant rather than the
cardinality of the set. The measure can be a restriction to the physical slab. -/
theorem separated_momentDecay_integral_le {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f μ) (hf0 : ∀ t, 0 ≤ f t) {A : ℕ} (hA : 2 ≤ A)
    {U : Finset ℝ} (hU : oneSeparated U) :
    (∑ u ∈ U, ∫ t, momentDecay A (t-u)*f t ∂μ) ≤
      separationMass * ∫ t, f t ∂μ := by
  have hi (u : ℝ) : Integrable (fun t => momentDecay A (t-u)*f t) μ :=
    integrable_momentDecay_mul hf A u
  rw [← integral_finsetSum _ (fun u _ => hi u), ← integral_const_mul]
  apply integral_mono (integrable_finsetSum _ (fun u _ => hi u)) (hf.const_mul _)
  intro t
  change (∑ u ∈ U, momentDecay A (t-u)*f t) ≤ separationMass*f t
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (separated_momentDecay_row hA hU t) (hf0 t)

end MathCollab.Density.Stronger
