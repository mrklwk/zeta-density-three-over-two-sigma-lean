module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Filter Set
open scoped Interval ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Young's inequality in the exact polynomial form used for weighted
twelfth-power Hölder. -/
theorem twelfth_tangent_bound {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    12 * a ^ 11 * x ≤ x ^ 12 + 11 * a ^ 12 := by
  have hpq : (12 : ℝ).HolderConjugate (12 / 11) := by
    norm_num [Real.holderConjugate_iff]
  have h := Real.young_inequality_of_nonneg hx (pow_nonneg ha 11) hpq
  have hp : (a ^ 11) ^ (12 / 11 : ℝ) = a ^ 12 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rw [hp] at h
  norm_num at h
  calc
    12 * a ^ 11 * x = 12 * (x * a ^ 11) := by ring
    _ ≤ 12 * (x ^ 12 / 12 + a ^ 12 / (12 / 11)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = x ^ 12 + 11 * a ^ 12 := by ring


/-- Weighted twelfth-power Hölder with the exact eleventh power of the
kernel mass. Its proof integrates Young's inequality and normalizes the
actual weighted mean; no moment estimate is a premise. -/
theorem integral_weighted_twelfth
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    (hwInt : Integrable w μ) (hwfInt : Integrable (fun x => w x * f x) μ)
    (hwfPowInt : Integrable (fun x => w x * f x ^ 12) μ)
    (hMass : 0 < ∫ x, w x ∂μ) :
    (∫ x, w x * f x ∂μ) ^ 12 ≤
      (∫ x, w x ∂μ) ^ 11 * ∫ x, w x * f x ^ 12 ∂μ := by
  let A : ℝ := (∫ x, w x * f x ∂μ) / (∫ x, w x ∂μ)
  have hA : 0 ≤ A := div_nonneg (integral_nonneg fun x => mul_nonneg (hw x) (hf x)) hMass.le
  have hmean : A * (∫ x, w x ∂μ) = ∫ x, w x * f x ∂μ := div_mul_cancel₀ _ hMass.ne'
  have hpoint (x : α) :
      (12 * A ^ 11) * (w x * f x) ≤ w x * f x ^ 12 + (11 * A ^ 12) * w x := by
    have h := mul_le_mul_of_nonneg_left (twelfth_tangent_bound hA (hf x)) (hw x)
    nlinarith
  have hInt := integral_mono (hwfInt.const_mul (12 * A ^ 11))
    (hwfPowInt.add (hwInt.const_mul (11 * A ^ 12))) hpoint
  dsimp only [Pi.add_apply] at hInt
  rw [integral_add hwfPowInt (hwInt.const_mul _), integral_const_mul, integral_const_mul] at hInt
  have hsmall : A ^ 12 * (∫ x, w x ∂μ) ≤ ∫ x, w x * f x ^ 12 ∂μ := by
    rw [← hmean] at hInt
    nlinarith
  calc
    _ = (∫ x, w x ∂μ) ^ 11 * (A ^ 12 * (∫ x, w x ∂μ)) := by rw [← hmean]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hMass.le 11)


end MathCollab.Density.Stronger
