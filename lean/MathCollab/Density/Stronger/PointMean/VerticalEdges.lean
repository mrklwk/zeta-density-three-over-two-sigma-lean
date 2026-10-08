module
-- Reversible module-visibility port of the audited development.
/-
Selected native vertical-edge and full-convolution point-mean proofs adapted
from Scott McColm, PointMeanLemmaThreeEdges.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
All off-critical estimates, reflection, double integration and horizontal
edges are proved dependencies; no point-mean or moment endpoint is assumed.
-/
public import MathCollab.Density.Stronger.PointMean.Reflection
public import MathCollab.Density.Stronger.PointMean.DoubleConvolution
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter
open MathCollab.Density.Contour
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

theorem integral_exp_neg_abs_heathBrown :
    (∫ x : ℝ, Real.exp (-|x|)) = 2 := by
  rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-x))]
  rw [integral_exp_neg_Ioi_zero]
  norm_num

theorem integrable_exp_neg_abs_heathBrown :
    Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  let f : ℝ → ℝ := fun x => Real.exp (-|x|)
  have hpos : IntegrableOn f (Ioi 0) := by
    apply (integrableOn_exp_neg_Ioi 0).congr_fun
      (fun x hx => by
        dsimp only [f]
        rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, f, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hall := hneg.union hpos
  rw [Iic_union_Ioi] at hall
  simpa only [IntegrableOn, Measure.restrict_univ] using hall

theorem heathBrownStrongSingularKernel_le_exp
    {delta x : ℝ} (hdelta : 0 < delta) :
    heathBrownStrongSingularKernel delta x ≤
      delta⁻¹ * Real.exp (-|x|) := by
  have hden : 0 < delta + |x| := by positivity
  have hExp : Real.exp (-(4 / 3 : ℝ) * |x|) ≤ Real.exp (-|x|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg x]
  unfold heathBrownStrongSingularKernel
  calc
    Real.exp (-(4 / 3 : ℝ) * |x|) / (delta + |x|) ≤
        Real.exp (-|x|) / (delta + |x|) := by gcongr
    _ ≤ Real.exp (-|x|) / delta := by
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hdelta
        (by linarith [abs_nonneg x])
    _ = delta⁻¹ * Real.exp (-|x|) := by field_simp

theorem integrable_heathBrownStrongSingularKernel
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (heathBrownStrongSingularKernel delta) := by
  apply ((integrable_exp_neg_abs_heathBrown.const_mul delta⁻¹)).mono'
  · have hcont : Continuous (heathBrownStrongSingularKernel delta) := by
      unfold heathBrownStrongSingularKernel
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x hx
        exact (by positivity : 0 < delta + |x|).ne' hx
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold heathBrownStrongSingularKernel
      positivity)]
    exact heathBrownStrongSingularKernel_le_exp hdelta

theorem integral_heathBrownStrongSingularKernel_le
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x : ℝ, heathBrownStrongSingularKernel delta x) ≤ 2 / delta := by
  calc
    (∫ x : ℝ, heathBrownStrongSingularKernel delta x) ≤
        ∫ x : ℝ, delta⁻¹ * Real.exp (-|x|) := by
      exact integral_mono
        (integrable_heathBrownStrongSingularKernel hdelta)
        (integrable_exp_neg_abs_heathBrown.const_mul delta⁻¹)
        (fun x => heathBrownStrongSingularKernel_le_exp hdelta)
    _ = delta⁻¹ * 2 := by
      rw [integral_const_mul, integral_exp_neg_abs_heathBrown]
    _ = 2 / delta := by field_simp

theorem intervalIntegral_heathBrownStrongSingularKernel_le
    {delta H : ℝ} (hdelta : 0 < delta) (hH : 0 ≤ H) :
    (∫ x in -H..H, heathBrownStrongSingularKernel delta x) ≤ 2 / delta := by
  calc
    (∫ x in -H..H, heathBrownStrongSingularKernel delta x) ≤
        ∫ x : ℝ, heathBrownStrongSingularKernel delta x := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_le_integral
        (integrable_heathBrownStrongSingularKernel hdelta)
        (Filter.Eventually.of_forall fun x => by
          unfold heathBrownStrongSingularKernel
          positivity)
    _ ≤ 2 / delta := integral_heathBrownStrongSingularKernel_le hdelta

theorem norm_VIntegral'_le_intervalIntegral_norm
    (f : ℂ → ℂ) {x a b : ℝ} (hab : a ≤ b) :
    ‖VIntegral' f x a b‖ ≤
      ∫ y in a..b, ‖f ((x : ℂ) + (y : ℂ) * I)‖ := by
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    nlinarith [mul_le_mul_of_nonneg_right hpiInv
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  unfold VIntegral' VIntegral
  rw [norm_smul, norm_smul]
  simp only [norm_I, one_mul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖∫ y in a..b, f ((x : ℂ) + (y : ℂ) * I)‖ ≤
      1 * ‖∫ y in a..b, f ((x : ℂ) + (y : ℂ) * I)‖ := by gcongr
    _ ≤ ∫ y in a..b, ‖f ((x : ℂ) + (y : ℂ) * I)‖ :=
      (by simpa only [one_mul] using
        (intervalIntegral.norm_integral_le_integral_norm hab :
          ‖∫ y in a..b, f ((x : ℂ) + (y : ℂ) * I)‖ ≤
            ∫ y in a..b, ‖f ((x : ℂ) + (y : ℂ) * I)‖))

theorem exists_norm_heathBrownLemmaThree_plusEdge_integrand_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t w : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t + w →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        C * (heathBrownStrongSingularKernel delta w *
          (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
  obtain ⟨G, hG, hGamma⟩ :=
    exists_heathBrown_Gamma_shift_kernel_strong_bound
  obtain ⟨P, hP, hPlus⟩ :=
    exists_heathBrown_offCritical_plus_strong_le
  refine ⟨G * P, mul_pos hG hP, ?_⟩
  intro delta t w hdelta hdeltaUpper htw
  have hden : 0 < delta + |w| := by positivity
  have hGamma' :
      ‖Complex.Gamma (((delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|) := by
    apply (le_div_iff₀ hden).2
    simpa only [mul_comm] using (hGamma delta w hdelta hdeltaUpper).1
  have hzeta := hPlus delta (t + w) hdelta hdeltaUpper htw
  have harg :
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
          (((delta : ℝ) : ℂ) + (w : ℂ) * I) =
        (((1 / 2 + delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow, harg]
  calc
    ‖Complex.Gamma (((delta : ℝ) : ℂ) + (w : ℂ) * I)‖ *
        ‖riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I)‖ ^
            (2 : ℕ) ≤
      (G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|)) *
        (P * (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      gcongr
    _ = (G * P) * (heathBrownStrongSingularKernel delta w *
          (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      unfold heathBrownStrongSingularKernel
      ring_nf

theorem integrable_heathBrownStrongLongEdgeMajorant
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun w : ℝ => heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
  convert (integrable_heathBrownStrongSingularKernel hdelta).add
    (integrable_strongKernel_mul_strongMoment hdelta t) using 1
  funext w
  simp only [Pi.add_apply]
  ring

theorem integral_heathBrownStrongLongEdgeMajorant_le
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) ≤
        ((2 + Real.pi) / delta) * (1 + heathBrownFullCriticalMoment t) := by
  have hfull := heathBrownFullCriticalMoment_nonneg t
  have hmass := integral_heathBrownStrongSingularKernel_le hdelta
  have hdouble := integral_strongKernel_mul_strongMoment_le hdelta t
  rw [show (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) =
        (∫ w : ℝ, heathBrownStrongSingularKernel delta w) +
          ∫ w : ℝ, heathBrownStrongSingularKernel delta w *
            heathBrownStrongMellinCriticalMoment delta (t + w) by
      rw [← integral_add
        (integrable_heathBrownStrongSingularKernel hdelta)
        (integrable_strongKernel_mul_strongMoment hdelta t)]
      apply integral_congr_ae
      filter_upwards with w
      ring]
  have hdeltaNonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  calc
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w) +
        ∫ w : ℝ, heathBrownStrongSingularKernel delta w *
          heathBrownStrongMellinCriticalMoment delta (t + w) ≤
      2 / delta + (Real.pi / delta) * heathBrownFullCriticalMoment t :=
        add_le_add hmass hdouble
    _ ≤ ((2 + Real.pi) / delta) * (1 + heathBrownFullCriticalMoment t) := by
      have hpi : 0 ≤ Real.pi := Real.pi_pos.le
      field_simp [hdelta.ne']
      nlinarith

theorem exists_norm_heathBrownLemmaThree_plusEdge_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t H : ℝ),
      0 < delta → delta ≤ 1 / 4 → 0 ≤ H → 10 + H ≤ t →
      ‖VIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) delta (-H) H‖ ≤
        (C / delta) * (1 + heathBrownFullCriticalMoment t) := by
  obtain ⟨B, hB, hPoint⟩ :=
    exists_norm_heathBrownLemmaThree_plusEdge_integrand_le
  let C : ℝ := B * (2 + Real.pi)
  have hC : 0 < C := mul_pos hB (by positivity)
  refine ⟨C, hC, ?_⟩
  intro delta t H hdelta hdeltaUpper hH ht
  let F : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := fun w => heathBrownStrongSingularKernel delta w *
    (1 + heathBrownStrongMellinCriticalMoment delta (t + w))
  have hg : Integrable g := by
    simpa only [g] using integrable_heathBrownStrongLongEdgeMajorant hdelta t
  have hNorm := norm_VIntegral'_le_intervalIntegral_norm F
    (x := delta) (a := -H) (b := H) (by linarith)
  calc
    ‖VIntegral' F delta (-H) H‖ ≤
        ∫ w in -H..H, ‖F ((delta : ℂ) + (w : ℂ) * I)‖ := hNorm
    _ ≤ ∫ w in -H..H, B * g w := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · have hcont := continuous_heathBrownZetaSquareMellinIntegrand_vertical
          (s := (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (a := delta) (by linarith) hdelta.ne'
          (by simp; linarith)
        have hcontNorm : Continuous (fun w : ℝ =>
            ‖F ((delta : ℂ) + (w : ℂ) * I)‖) := by
          simpa only [F] using hcont.norm
        exact hcontNorm.intervalIntegrable _ _
      · exact (hg.const_mul B).intervalIntegrable
      · intro w hw'
        simpa only [F, g] using hPoint delta t w hdelta hdeltaUpper
          (by linarith [hw'.1])
    _ = B * ∫ w in -H..H, g w := intervalIntegral.integral_const_mul _ _
    _ ≤ B * ∫ w : ℝ, g w := by
      gcongr
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_le_integral hg
        (Filter.Eventually.of_forall fun w => by
          dsimp only [g]
          have hm := heathBrownStrongMellinCriticalMoment_nonneg
            (delta := delta) (t := t + w) hdelta
          unfold heathBrownStrongSingularKernel
          positivity)
    _ ≤ B * (((2 + Real.pi) / delta) *
          (1 + heathBrownFullCriticalMoment t)) := by
      gcongr
      simpa only [g] using integral_heathBrownStrongLongEdgeMajorant_le hdelta t
    _ = (C / delta) * (1 + heathBrownFullCriticalMoment t) := by
      dsimp only [C]
      ring

theorem exists_norm_heathBrownLemmaThree_minusEdge_integrand_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t w : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t + w →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        C * Real.exp
          (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) *
            (heathBrownStrongSingularKernel delta w *
              (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
  obtain ⟨G, hG, hGamma⟩ :=
    exists_heathBrown_Gamma_shift_kernel_strong_bound
  obtain ⟨P, D, hP, hD, hMinus⟩ :=
    exists_heathBrown_offCritical_minus_strong_le
  refine ⟨G * P, D, mul_pos hG hP, hD, ?_⟩
  intro delta t w hdelta hdeltaUpper htw
  have hden : 0 < delta + |w| := by positivity
  have hGamma' :
      ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|) := by
    apply (le_div_iff₀ hden).2
    simpa only [mul_comm] using (hGamma delta w hdelta hdeltaUpper).2
  have hzeta := hMinus delta (t + w) hdelta hdeltaUpper htw
  have harg :
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
          (((-delta : ℝ) : ℂ) + (w : ℂ) * I) =
        (((1 / 2 - delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow, harg]
  calc
    ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ *
        ‖riemannZeta
          (((1 / 2 - delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I)‖ ^
            (2 : ℕ) ≤
      (G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|)) *
        (P * Real.exp
          (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) *
            (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      gcongr
    _ = (G * P) * Real.exp
          (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) *
            (heathBrownStrongSingularKernel delta w *
              (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      unfold heathBrownStrongSingularKernel
      ring_nf

theorem exists_norm_heathBrownLemmaThree_minusEdge_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t H Q : ℝ),
      0 < delta → delta ≤ 1 / 4 → 0 ≤ H → 10 + H ≤ t → 0 ≤ Q →
      (∀ w ∈ Set.Icc (-H) H,
        Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) ≤ Q) →
      ‖VIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) (-delta) (-H) H‖ ≤
        ((C * Q) / delta) * (1 + heathBrownFullCriticalMoment t) := by
  obtain ⟨B, D, hB, hD, hPoint⟩ :=
    exists_norm_heathBrownLemmaThree_minusEdge_integrand_le
  let C : ℝ := B * (2 + Real.pi)
  have hC : 0 < C := mul_pos hB (by positivity)
  refine ⟨C, D, hC, hD, ?_⟩
  intro delta t H Q hdelta hdeltaUpper hH ht hQ hUniform
  let F : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := fun w => heathBrownStrongSingularKernel delta w *
    (1 + heathBrownStrongMellinCriticalMoment delta (t + w))
  have hg : Integrable g := by
    simpa only [g] using integrable_heathBrownStrongLongEdgeMajorant hdelta t
  have hNorm := norm_VIntegral'_le_intervalIntegral_norm F
    (x := -delta) (a := -H) (b := H) (by linarith)
  calc
    ‖VIntegral' F (-delta) (-H) H‖ ≤
        ∫ w in -H..H, ‖F (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ := hNorm
    _ ≤ ∫ w in -H..H, (B * Q) * g w := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · have hcont := continuous_heathBrownZetaSquareMellinIntegrand_vertical
          (s := (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (a := -delta) (by linarith) (neg_ne_zero.mpr hdelta.ne')
          (by simp; linarith)
        have hcontNorm : Continuous (fun w : ℝ =>
            ‖F (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖) := by
          simpa only [F] using hcont.norm
        exact hcontNorm.intervalIntegrable _ _
      · exact (hg.const_mul (B * Q)).intervalIntegrable
      · intro w hw
        have hraw := hPoint delta t w hdelta hdeltaUpper
          (by linarith [hw.1])
        have hfactor := hUniform w hw
        have hgNonneg : 0 ≤ g w := by
          dsimp only [g]
          have hm := heathBrownStrongMellinCriticalMoment_nonneg
            (delta := delta) (t := t + w) hdelta
          unfold heathBrownStrongSingularKernel
          positivity
        calc
          ‖F (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
              B * Real.exp
                (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) * g w := by
            simpa only [F, g] using hraw
          _ ≤ B * Q * g w := by gcongr
          _ = (B * Q) * g w := by ring
    _ = (B * Q) * ∫ w in -H..H, g w :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (B * Q) * ∫ w : ℝ, g w := by
      gcongr
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_le_integral hg
        (Filter.Eventually.of_forall fun w => by
          dsimp only [g]
          have hm := heathBrownStrongMellinCriticalMoment_nonneg
            (delta := delta) (t := t + w) hdelta
          unfold heathBrownStrongSingularKernel
          positivity)
    _ ≤ (B * Q) * (((2 + Real.pi) / delta) *
          (1 + heathBrownFullCriticalMoment t)) := by
      gcongr
      simpa only [g] using integral_heathBrownStrongLongEdgeMajorant_le hdelta t
    _ = ((C * Q) / delta) * (1 + heathBrownFullCriticalMoment t) := by
      dsimp only [C]
      ring

theorem heathBrownLemmaThree_minus_factor_le_exp_four
    {D t w : ℝ} (ht : 8 ≤ t)
    (hRadius : heathBrownLemmaThreeRadius t ≤ t / 2)
    (hDlog : D ≤ Real.log t)
    (hw : w ∈ Set.Icc (-heathBrownLemmaThreeRadius t)
      (heathBrownLemmaThreeRadius t)) :
    Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) *
      heathBrownLemmaThreeDelta t) ≤ Real.exp 4 := by
  have htPos : 0 < t := by linarith
  have htwLower : -(t / 2) ≤ w := by linarith [hw.1]
  have hargPos : 0 < (t + w) / 2 + 2 := by linarith
  have hargUpper : (t + w) / 2 + 2 ≤ t := by linarith [hw.2]
  have hlogUpper : Real.log ((t + w) / 2 + 2) ≤ Real.log t :=
    Real.log_le_log hargPos hargUpper
  have hlogPos : 0 < Real.log t := Real.log_pos (by linarith)
  apply Real.exp_le_exp.mpr
  unfold heathBrownLemmaThreeDelta
  calc
    2 * (Real.log ((t + w) / 2 + 2) + D) * (1 / Real.log t) =
        (2 * (Real.log ((t + w) / 2 + 2) + D)) / Real.log t := by ring
    _ ≤ 4 := (div_le_iff₀ hlogPos).2 (by nlinarith)

theorem eventually_heathBrownLemmaThree_minus_factor
    (D : ℝ) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ w ∈
      Set.Icc (-heathBrownLemmaThreeRadius t) (heathBrownLemmaThreeRadius t),
      Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) *
        heathBrownLemmaThreeDelta t) ≤ Real.exp 4 := by
  have hD := Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop D)
  filter_upwards [eventually_heathBrownLemmaThreeRadius_le_half_identity,
    hD, Filter.eventually_ge_atTop (8 : ℝ)] with t hRadius hDlog ht
  intro w hw
  exact heathBrownLemmaThree_minus_factor_le_exp_four ht hRadius hDlog hw

theorem exists_eventually_heathBrownLemmaThree_fullMoment :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in Filter.atTop,
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t * (1 + heathBrownFullCriticalMoment t) := by
  obtain ⟨P, hP, hPlus⟩ :=
    exists_norm_heathBrownLemmaThree_plusEdge_le
  obtain ⟨M, D, hM, hD, hMinus⟩ :=
    exists_norm_heathBrownLemmaThree_minusEdge_le
  let C : ℝ := 2 + P + M * Real.exp 4
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hMinusFactor := eventually_heathBrownLemmaThree_minus_factor D
  filter_upwards [eventually_norm_heathBrownLemmaThree_horizontalEdges_le_one,
    eventually_heathBrownLemmaThreeRadius_le_half_identity,
    hMinusFactor, Real.tendsto_log_atTop.eventually
      (Filter.eventually_ge_atTop (4 : ℝ)),
    Filter.eventually_ge_atTop (20 : ℝ)] with
      t hHorizontal hRadius hFactor hlog ht
  let delta : ℝ := heathBrownLemmaThreeDelta t
  let H : ℝ := heathBrownLemmaThreeRadius t
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  let f : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand s
  let bottom : ℂ := HIntegral' f (-delta) delta (-H)
  let top : ℂ := HIntegral' f (-delta) delta H
  let plus : ℂ := VIntegral' f delta (-H) H
  let minus : ℂ := VIntegral' f (-delta) (-H) H
  let Z : ℝ := heathBrownFullCriticalMoment t
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact heathBrownLemmaThreeDelta_pos (by linarith)
  have hdeltaUpper : delta ≤ 1 / 4 := by
    dsimp only [delta, heathBrownLemmaThreeDelta]
    exact one_div_le_one_div_of_le (by norm_num) hlog
  have hH : 0 ≤ H := by
    dsimp only [H, heathBrownLemmaThreeRadius]
    positivity
  have htH : 10 + H ≤ t := by
    dsimp only [H]
    linarith
  have hBottom : ‖bottom‖ ≤ 1 := by
    simpa only [bottom, f, s, delta, H] using hHorizontal.1
  have hTop : ‖top‖ ≤ 1 := by
    simpa only [top, f, s, delta, H] using hHorizontal.2
  have hPlus : ‖plus‖ ≤ (P / delta) * (1 + Z) := by
    simpa only [plus, f, s, Z] using
      hPlus delta t H hdelta hdeltaUpper hH htH
  have hMinus : ‖minus‖ ≤ ((M * Real.exp 4) / delta) * (1 + Z) := by
    apply hMinus delta t H (Real.exp 4) hdelta hdeltaUpper hH htH
      (Real.exp_pos _).le
    simpa only [H] using hFactor
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact heathBrownFullCriticalMoment_nonneg t
  have hRect := heathBrownLemmaThree_finiteRectangle t (by linarith)
  have hEdges := heathBrownLemmaThree_rectangle_eq_edges t
  have hIdentity : riemannZeta s ^ 2 = bottom - top + plus - minus := by
    rw [← hRect, hEdges]
  have hNorm : ‖riemannZeta s ^ 2‖ ≤
      ‖bottom‖ + ‖top‖ + ‖plus‖ + ‖minus‖ := by
    rw [hIdentity]
    have hOuter := norm_sub_le (bottom - top + plus) minus
    have hMiddle := norm_add_le (bottom - top) plus
    have hInner := norm_sub_le bottom top
    linarith
  have hdeltaInv : 1 / delta = Real.log t := by
    dsimp only [delta, heathBrownLemmaThreeDelta]
    field_simp [(by linarith : Real.log t ≠ 0)]
  calc
    zetaMomentCriticalNorm t ^ (2 : ℕ) = ‖riemannZeta s ^ 2‖ := by
      dsimp only [zetaMomentCriticalNorm, s]
      rw [norm_pow]
    _ ≤ ‖bottom‖ + ‖top‖ + ‖plus‖ + ‖minus‖ := hNorm
    _ ≤ 2 + (P / delta) * (1 + Z) +
          ((M * Real.exp 4) / delta) * (1 + Z) := by linarith
    _ ≤ C * (1 / delta) * (1 + Z) := by
      have hInv : 1 ≤ 1 / delta := by
        rw [hdeltaInv]
        linarith
      have hOneZ : 1 ≤ 1 + Z := by linarith
      have hProd : 1 ≤ (1 / delta) * (1 + Z) := by
        calc
          1 ≤ 1 / delta := hInv
          _ = (1 / delta) * 1 := by ring
          _ ≤ (1 / delta) * (1 + Z) :=
            mul_le_mul_of_nonneg_left hOneZ (by positivity)
      dsimp only [C]
      calc
        2 + (P / delta) * (1 + Z) +
            ((M * Real.exp 4) / delta) * (1 + Z) ≤
          2 * ((1 / delta) * (1 + Z)) + (P / delta) * (1 + Z) +
            ((M * Real.exp 4) / delta) * (1 + Z) := by
              nlinarith [hProd]
        _ = (2 + P + M * Real.exp 4) * (1 / delta) * (1 + Z) := by ring
    _ = C * Real.log t * (1 + heathBrownFullCriticalMoment t) := by
      rw [hdeltaInv]

end MathCollab.Density.Stronger.PointMean
