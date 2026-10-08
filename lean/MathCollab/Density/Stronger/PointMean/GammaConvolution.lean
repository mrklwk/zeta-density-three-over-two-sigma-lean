module
-- Reversible module-visibility port of the audited development.
/-
Selected singular-kernel convolution proofs adapted from Scott McColm,
PointMeanGammaConvolution.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_RECTANGLE_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
Only mathlib integral facts are imported. No zeta or moment estimate is assumed.
-/
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The square-integrable reserve left after taking one unit of exponential
decay out of the product of two strong Gamma bounds. -/
noncomputable def heathBrownGammaReserveKernel (delta x : ℝ) : ℝ :=
  Real.exp (-|x| / 6) / (delta + |x|)

theorem integrable_inv_delta_sq_add_sq {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun x : ℝ => (delta ^ 2 + x ^ 2)⁻¹) := by
  have hbase : Integrable (fun x : ℝ => (1 + (x / delta) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div hdelta.ne'
  have hscaled := hbase.const_mul (delta ^ 2)⁻¹
  convert hscaled using 1
  funext x
  field_simp [hdelta.ne']

theorem integral_inv_delta_sq_add_sq {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x : ℝ, (delta ^ 2 + x ^ 2)⁻¹) = Real.pi / delta := by
  let f : ℝ → ℝ := fun x => (1 + x ^ 2)⁻¹
  have hchange := MeasureTheory.Measure.integral_comp_div f delta
  calc
    (∫ x : ℝ, (delta ^ 2 + x ^ 2)⁻¹) =
        ∫ x : ℝ, (delta ^ 2)⁻¹ * f (x / delta) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp only [f]
          field_simp [hdelta.ne']
    _ = (delta ^ 2)⁻¹ * ∫ x : ℝ, f (x / delta) :=
      integral_const_mul _ _
    _ = (delta ^ 2)⁻¹ * (|delta| * ∫ x : ℝ, f x) := by
      rw [hchange]
      rfl
    _ = Real.pi / delta := by
      rw [abs_of_pos hdelta]
      simp only [f, integral_univ_inv_one_add_sq]
      field_simp [hdelta.ne']

theorem heathBrownGammaReserveKernel_sq_le
    {delta x : ℝ} (hdelta : 0 < delta) :
    heathBrownGammaReserveKernel delta x ^ (2 : ℕ) ≤
      (delta ^ 2 + x ^ 2)⁻¹ := by
  have hden : 0 < delta + |x| := by positivity
  have hsmall : 0 < delta ^ 2 + x ^ 2 := by positivity
  have hdenCompare : delta ^ 2 + x ^ 2 ≤ (delta + |x|) ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x]
  have hexp : Real.exp (-|x| / 6) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [abs_nonneg x]
  have hexpSq : Real.exp (-|x| / 6) ^ (2 : ℕ) ≤ 1 := by
    nlinarith [Real.exp_pos (-|x| / 6)]
  unfold heathBrownGammaReserveKernel
  calc
    (Real.exp (-|x| / 6) / (delta + |x|)) ^ (2 : ℕ) =
        Real.exp (-|x| / 6) ^ (2 : ℕ) / (delta + |x|) ^ (2 : ℕ) :=
      div_pow _ _ _
    _ ≤ 1 / (delta + |x|) ^ (2 : ℕ) := by
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).2 hexpSq
    _ ≤ 1 / (delta ^ 2 + x ^ 2) :=
      one_div_le_one_div_of_le hsmall hdenCompare
    _ = (delta ^ 2 + x ^ 2)⁻¹ := one_div _

theorem integrable_heathBrownGammaReserveKernel_sq
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun x : ℝ =>
      heathBrownGammaReserveKernel delta x ^ (2 : ℕ)) := by
  apply (integrable_inv_delta_sq_add_sq hdelta).mono'
  · have hcont : Continuous (fun x : ℝ =>
        heathBrownGammaReserveKernel delta x ^ (2 : ℕ)) := by
      unfold heathBrownGammaReserveKernel
      apply Continuous.pow
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x hx
        exact (by positivity : 0 < delta + |x|).ne' hx
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact heathBrownGammaReserveKernel_sq_le hdelta

theorem integral_heathBrownGammaReserveKernel_sq_le
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x : ℝ, heathBrownGammaReserveKernel delta x ^ (2 : ℕ)) ≤
      Real.pi / delta := by
  rw [← integral_inv_delta_sq_add_sq hdelta]
  exact integral_mono
    (integrable_heathBrownGammaReserveKernel_sq hdelta)
    (integrable_inv_delta_sq_add_sq hdelta)
    (fun x => heathBrownGammaReserveKernel_sq_le hdelta)

/-- Product of the two literal strong Gamma majorants before convolution. -/
noncomputable def heathBrownStrongGammaConvolutionIntegrand
    (delta u w : ℝ) : ℝ :=
  (Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|)) *
    (Real.exp (-(4 / 3 : ℝ) * |u - w|) / (delta + |u - w|))

theorem heathBrownStrongGammaConvolutionIntegrand_nonneg
    {delta u w : ℝ} (hdelta : 0 < delta) :
    0 ≤ heathBrownStrongGammaConvolutionIntegrand delta u w := by
  unfold heathBrownStrongGammaConvolutionIntegrand
  positivity

theorem heathBrown_strong_exponential_reserve (u w : ℝ) :
    Real.exp (-(4 / 3 : ℝ) * |w|) *
        Real.exp (-(4 / 3 : ℝ) * |u - w|) ≤
      Real.exp (-|u|) * Real.exp (-|w| / 6) *
        Real.exp (-|u - w| / 6) := by
  have htri : |u| ≤ |w| + |u - w| := by
    calc
      |u| = |w + (u - w)| := by ring_nf
      _ ≤ |w| + |u - w| := abs_add_le _ _
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w, abs_nonneg (u - w)])

theorem heathBrownStrongGammaConvolutionIntegrand_le
    {delta u w : ℝ} (hdelta : 0 < delta) :
    heathBrownStrongGammaConvolutionIntegrand delta u w ≤
      Real.exp (-|u|) / 2 *
        (heathBrownGammaReserveKernel delta w ^ (2 : ℕ) +
          heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) := by
  let a := heathBrownGammaReserveKernel delta w
  let b := heathBrownGammaReserveKernel delta (u - w)
  have ha : 0 ≤ a := by unfold a heathBrownGammaReserveKernel; positivity
  have hb : 0 ≤ b := by unfold b heathBrownGammaReserveKernel; positivity
  have hab : a * b ≤ (a ^ (2 : ℕ) + b ^ (2 : ℕ)) / 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hdenW : 0 < delta + |w| := by positivity
  have hdenUW : 0 < delta + |u - w| := by positivity
  have hreserve := heathBrown_strong_exponential_reserve u w
  have hdiv :
      (Real.exp (-(4 / 3 : ℝ) * |w|) *
          Real.exp (-(4 / 3 : ℝ) * |u - w|)) /
          ((delta + |w|) * (delta + |u - w|)) ≤
        (Real.exp (-|u|) * Real.exp (-|w| / 6) *
          Real.exp (-|u - w| / 6)) /
          ((delta + |w|) * (delta + |u - w|)) := by
    exact div_le_div_of_nonneg_right hreserve (by positivity)
  calc
    heathBrownStrongGammaConvolutionIntegrand delta u w =
        (Real.exp (-(4 / 3 : ℝ) * |w|) *
          Real.exp (-(4 / 3 : ℝ) * |u - w|)) /
          ((delta + |w|) * (delta + |u - w|)) := by
      unfold heathBrownStrongGammaConvolutionIntegrand
      field_simp
    _ ≤ (Real.exp (-|u|) * Real.exp (-|w| / 6) *
          Real.exp (-|u - w| / 6)) /
          ((delta + |w|) * (delta + |u - w|)) := hdiv
    _ = Real.exp (-|u|) * (a * b) := by
      unfold a b heathBrownGammaReserveKernel
      field_simp
    _ ≤ Real.exp (-|u|) *
        ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) / 2) := by
      gcongr
    _ = Real.exp (-|u|) / 2 *
        (heathBrownGammaReserveKernel delta w ^ (2 : ℕ) +
          heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) := by
      unfold a b
      ring

theorem integrable_heathBrownGammaReserveKernel_sq_sub
    {delta : ℝ} (hdelta : 0 < delta) (u : ℝ) :
    Integrable (fun w : ℝ =>
      heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) := by
  have h := (integrable_heathBrownGammaReserveKernel_sq hdelta).comp_sub_right u
  convert h using 1
  funext w
  unfold heathBrownGammaReserveKernel
  rw [abs_sub_comm]

theorem integral_heathBrownGammaReserveKernel_sq_sub (delta u : ℝ) :
    (∫ w : ℝ, heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) =
      ∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ) := by
  calc
    (∫ w : ℝ, heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) =
        ∫ w : ℝ, heathBrownGammaReserveKernel delta (w - u) ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards with w
      unfold heathBrownGammaReserveKernel
      rw [abs_sub_comm]
    _ = ∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ) := by
      exact integral_sub_right_eq_self
        (fun w : ℝ => heathBrownGammaReserveKernel delta w ^ (2 : ℕ))
        u (μ := volume)

theorem integrable_heathBrownStrongGammaConvolutionIntegrand
    {delta u : ℝ} (hdelta : 0 < delta) :
    Integrable (heathBrownStrongGammaConvolutionIntegrand delta u) := by
  let major : ℝ → ℝ := fun w => Real.exp (-|u|) / 2 *
    (heathBrownGammaReserveKernel delta w ^ (2 : ℕ) +
      heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ))
  have hmajor : Integrable major := by
    exact ((integrable_heathBrownGammaReserveKernel_sq hdelta).add
      (integrable_heathBrownGammaReserveKernel_sq_sub hdelta u)).const_mul
        (Real.exp (-|u|) / 2)
  apply hmajor.mono'
  · have hcont : Continuous
        (heathBrownStrongGammaConvolutionIntegrand delta u) := by
      unfold heathBrownStrongGammaConvolutionIntegrand
      apply Continuous.mul
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro w hw
          exact (by positivity : 0 < delta + |w|).ne' hw
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro w hw
          exact (by positivity : 0 < delta + |u - w|).ne' hw
    exact hcont.aestronglyMeasurable
  · filter_upwards with w
    rw [Real.norm_eq_abs,
      abs_of_nonneg (heathBrownStrongGammaConvolutionIntegrand_nonneg hdelta)]
    exact heathBrownStrongGammaConvolutionIntegrand_le hdelta

/-- The exact convolution estimate needed on the two vertical edges.  In
particular, the loss is `delta⁻¹`, not `delta⁻²`. -/
theorem integral_heathBrownStrongGammaConvolutionIntegrand_le
    {delta u : ℝ} (hdelta : 0 < delta) :
    (∫ w : ℝ, heathBrownStrongGammaConvolutionIntegrand delta u w) ≤
      (Real.pi / delta) * Real.exp (-|u|) := by
  let k : ℝ → ℝ := fun w =>
    heathBrownGammaReserveKernel delta w ^ (2 : ℕ)
  have hk := integrable_heathBrownGammaReserveKernel_sq hdelta
  have hks := integrable_heathBrownGammaReserveKernel_sq_sub hdelta u
  have hmono :
      (∫ w : ℝ, heathBrownStrongGammaConvolutionIntegrand delta u w) ≤
        ∫ w : ℝ, Real.exp (-|u|) / 2 *
          (k w + k (u - w)) := by
    apply integral_mono
      (integrable_heathBrownStrongGammaConvolutionIntegrand hdelta)
      ((hk.add hks).const_mul (Real.exp (-|u|) / 2))
    intro w
    exact heathBrownStrongGammaConvolutionIntegrand_le hdelta
  calc
    (∫ w : ℝ, heathBrownStrongGammaConvolutionIntegrand delta u w) ≤
        ∫ w : ℝ, Real.exp (-|u|) / 2 * (k w + k (u - w)) := hmono
    _ = Real.exp (-|u|) / 2 *
        ((∫ w : ℝ, k w) + ∫ w : ℝ, k (u - w)) := by
      rw [integral_const_mul, integral_add hk hks]
    _ = Real.exp (-|u|) / 2 * (2 * ∫ w : ℝ, k w) := by
      rw [integral_heathBrownGammaReserveKernel_sq_sub delta u]
      ring
    _ ≤ Real.exp (-|u|) / 2 * (2 * (Real.pi / delta)) := by
      gcongr
      exact integral_heathBrownGammaReserveKernel_sq_le hdelta
    _ = (Real.pi / delta) * Real.exp (-|u|) := by ring

end MathCollab.Density.Stronger.PointMean
