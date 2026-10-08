module
-- Reversible module-visibility port of the audited development.
/-
Selected literal critical-moment double convolution proofs adapted from
Scott McColm, PointMeanLemmaThreeDouble.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.PointMean.OffCriticalPositive
public import MathCollab.Density.Stronger.PointMean.GammaConvolution

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

noncomputable def heathBrownStrongSingularKernel (delta x : ℝ) : ℝ :=
  Real.exp (-(4 / 3 : ℝ) * |x|) / (delta + |x|)

noncomputable def heathBrownCriticalWeighted (t u : ℝ) : ℝ :=
  Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

theorem integrable_heathBrownCriticalWeighted (t : ℝ) :
    Integrable (heathBrownCriticalWeighted t) := by
  simpa only [heathBrownCriticalWeighted, heathBrownFullCriticalMoment] using!
    integrable_heathBrownFullCriticalMoment t

theorem heathBrownCriticalWeighted_nonneg (t u : ℝ) :
    0 ≤ heathBrownCriticalWeighted t u := by
  unfold heathBrownCriticalWeighted
  positivity

theorem integrable_heathBrown_reserve_sq_mul_critical_add
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) := by
  let r : ℝ → ℝ := fun w =>
    heathBrownGammaReserveKernel delta w ^ (2 : ℕ)
  let h : ℝ → ℝ := heathBrownCriticalWeighted t
  have hr : Integrable r := by
    simpa only [r] using integrable_heathBrownGammaReserveKernel_sq hdelta
  have hh : Integrable h := by
    simpa only [h] using integrable_heathBrownCriticalWeighted t
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      r p.1 * h (p.1 + p.2)) (volume.prod volume) := by
    have hcont : Continuous (fun p : ℝ × ℝ => r p.1 * h (p.1 + p.2)) := by
      dsimp only [r, h, heathBrownGammaReserveKernel,
        heathBrownCriticalWeighted]
      apply Continuous.mul
      · apply Continuous.pow
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro p hp
          exact (by positivity : 0 < delta + |p.1|).ne' hp
      · apply Continuous.mul
        · fun_prop
        · exact (continuous_zetaMomentCriticalNorm.pow 2).comp (by fun_prop)
    exact hcont.aestronglyMeasurable
  change Integrable (fun p : ℝ × ℝ => r p.1 * h (p.1 + p.2)) volume
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with w
    have hshift := hh.comp_sub_right (-w)
    have hmul := hshift.mul_const (r w)
    convert hmul using 1
    funext v
    simp only [sub_neg_eq_add]
    ring_nf
  · let I : ℝ := ∫ u : ℝ, ‖h u‖
    have houter : Integrable (fun w : ℝ => I * r w) := hr.const_mul I
    convert houter using 1
    funext w
    have hshiftIntegral : (∫ v : ℝ, ‖h (w + v)‖) = I := by
      calc
        (∫ v : ℝ, ‖h (w + v)‖) = ∫ v : ℝ, ‖h (v - (-w))‖ := by
          apply integral_congr_ae
          filter_upwards with v
          congr 2
          ring_nf
        _ = ∫ v : ℝ, ‖h v‖ :=
          integral_sub_right_eq_self (fun v : ℝ => ‖h v‖) (-w) (μ := volume)
        _ = I := rfl
    have hrw : 0 ≤ r w := by
      dsimp only [r, heathBrownGammaReserveKernel]
      positivity
    calc
      (∫ v : ℝ, ‖r w * h (w + v)‖) =
          r w * ∫ v : ℝ, ‖h (w + v)‖ := by
        simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hrw]
        exact integral_const_mul _ _
      _ = r w * I := by rw [hshiftIntegral]
      _ = I * r w := by ring_nf

theorem integral_heathBrown_reserve_sq_mul_critical_add
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ p : ℝ × ℝ,
      heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) =
      (∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ)) *
        heathBrownFullCriticalMoment t := by
  let r : ℝ → ℝ := fun w =>
    heathBrownGammaReserveKernel delta w ^ (2 : ℕ)
  let h : ℝ → ℝ := heathBrownCriticalWeighted t
  have hprod := integrable_heathBrown_reserve_sq_mul_critical_add hdelta t
  have hh : Integrable h := by
    simpa only [h] using integrable_heathBrownCriticalWeighted t
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hprod ⊢
  rw [integral_prod _ hprod]
  change (∫ w : ℝ, ∫ v : ℝ, r w * h (w + v)) = _
  have hinner : ∀ w : ℝ,
      (∫ v : ℝ, r w * h (w + v)) = r w * ∫ u : ℝ, h u := by
    intro w
    rw [integral_const_mul]
    congr 1
    calc
      (∫ v : ℝ, h (w + v)) = ∫ v : ℝ, h (v - (-w)) := by
        apply integral_congr_ae
        filter_upwards with v
        congr 1
        ring_nf
      _ = ∫ u : ℝ, h u :=
        integral_sub_right_eq_self h (-w) (μ := volume)
  simp_rw [hinner]
  rw [integral_mul_const]
  unfold r h heathBrownCriticalWeighted heathBrownFullCriticalMoment
  rfl

theorem integrable_heathBrown_reserve_sq_snd_mul_critical_add
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) := by
  have h := (integrable_heathBrown_reserve_sq_mul_critical_add hdelta t).swap
  convert h using 1
  funext p
  change heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
      heathBrownCriticalWeighted t (p.1 + p.2) =
    heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
      heathBrownCriticalWeighted t (p.2 + p.1)
  rw [add_comm p.2 p.1]

theorem integral_heathBrown_reserve_sq_snd_mul_critical_add
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ p : ℝ × ℝ,
      heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) =
      (∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ)) *
        heathBrownFullCriticalMoment t := by
  let f : ℝ × ℝ → ℝ := fun p =>
    heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
      heathBrownCriticalWeighted t (p.1 + p.2)
  have hswap := integral_prod_swap (μ := volume) (ν := volume) f
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  calc
    (∫ p : ℝ × ℝ,
      heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2) ∂volume.prod volume) =
      ∫ p : ℝ × ℝ, f p.swap ∂volume.prod volume := by
        apply integral_congr_ae
        filter_upwards with p
        rcases p with ⟨p, q⟩
        simp only [f, Prod.swap_prod_mk]
        rw [add_comm q p]
    _ = ∫ p : ℝ × ℝ, f p ∂volume.prod volume := hswap
    _ = _ := by
      rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      exact integral_heathBrown_reserve_sq_mul_critical_add hdelta t

noncomputable def heathBrownStrongDoubleIntegrand
    (delta t : ℝ) (p : ℝ × ℝ) : ℝ :=
  heathBrownStrongSingularKernel delta p.1 *
    heathBrownStrongSingularKernel delta p.2 *
      zetaMomentCriticalNorm (t + p.1 + p.2) ^ (2 : ℕ)

noncomputable def heathBrownStrongDoubleMajorant
    (delta t : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) +
      heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ)) *
        heathBrownCriticalWeighted t (p.1 + p.2)

theorem heathBrownStrongDoubleIntegrand_nonneg
    {delta t : ℝ} (hdelta : 0 < delta) (p : ℝ × ℝ) :
    0 ≤ heathBrownStrongDoubleIntegrand delta t p := by
  unfold heathBrownStrongDoubleIntegrand heathBrownStrongSingularKernel
  positivity

theorem heathBrownStrongDoubleIntegrand_le
    {delta t : ℝ} (hdelta : 0 < delta) (p : ℝ × ℝ) :
    heathBrownStrongDoubleIntegrand delta t p ≤
      heathBrownStrongDoubleMajorant delta t p := by
  rcases p with ⟨w, v⟩
  have hkernel := heathBrownStrongGammaConvolutionIntegrand_le
    (delta := delta) (u := w + v) (w := w) hdelta
  have hkernel' :
      heathBrownStrongSingularKernel delta w *
          heathBrownStrongSingularKernel delta v ≤
        Real.exp (-|w + v|) / 2 *
          (heathBrownGammaReserveKernel delta w ^ (2 : ℕ) +
            heathBrownGammaReserveKernel delta v ^ (2 : ℕ)) := by
    simpa only [heathBrownStrongSingularKernel,
      heathBrownStrongGammaConvolutionIntegrand,
      show w + v - w = v by ring] using hkernel
  unfold heathBrownStrongDoubleIntegrand heathBrownStrongDoubleMajorant
  have hz : 0 ≤ zetaMomentCriticalNorm (t + w + v) ^ (2 : ℕ) :=
    sq_nonneg _
  calc
    heathBrownStrongSingularKernel delta w *
        heathBrownStrongSingularKernel delta v *
          zetaMomentCriticalNorm (t + w + v) ^ (2 : ℕ) ≤
      (Real.exp (-|w + v|) / 2 *
        (heathBrownGammaReserveKernel delta w ^ (2 : ℕ) +
          heathBrownGammaReserveKernel delta v ^ (2 : ℕ))) *
            zetaMomentCriticalNorm (t + w + v) ^ (2 : ℕ) := by
      gcongr
    _ = (1 / 2 : ℝ) *
        (heathBrownGammaReserveKernel delta w ^ (2 : ℕ) +
          heathBrownGammaReserveKernel delta v ^ (2 : ℕ)) *
            heathBrownCriticalWeighted t (w + v) := by
      unfold heathBrownCriticalWeighted
      rw [show t + (w + v) = t + w + v by ring]
      ring

theorem integrable_heathBrownStrongDoubleMajorant
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (heathBrownStrongDoubleMajorant delta t) := by
  have hfst := integrable_heathBrown_reserve_sq_mul_critical_add hdelta t
  have hsnd := integrable_heathBrown_reserve_sq_snd_mul_critical_add hdelta t
  have hsum := hfst.add hsnd
  have hhalf := hsum.const_mul (1 / 2 : ℝ)
  convert hhalf using 1
  funext p
  unfold heathBrownStrongDoubleMajorant
  simp only [Pi.add_apply]
  ring

theorem integrable_heathBrownStrongDoubleIntegrand
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (heathBrownStrongDoubleIntegrand delta t) := by
  apply (integrable_heathBrownStrongDoubleMajorant hdelta t).mono'
  · have hcont : Continuous (heathBrownStrongDoubleIntegrand delta t) := by
      unfold heathBrownStrongDoubleIntegrand heathBrownStrongSingularKernel
      apply Continuous.mul
      · apply Continuous.mul
        · apply Continuous.div
          · fun_prop
          · fun_prop
          · intro p hp
            exact (by positivity : 0 < delta + |p.1|).ne' hp
        · apply Continuous.div
          · fun_prop
          · fun_prop
          · intro p hp
            exact (by positivity : 0 < delta + |p.2|).ne' hp
      · exact (continuous_zetaMomentCriticalNorm.pow 2).comp (by fun_prop)
    exact hcont.aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs,
      abs_of_nonneg (heathBrownStrongDoubleIntegrand_nonneg hdelta p)]
    exact heathBrownStrongDoubleIntegrand_le hdelta p

theorem integral_heathBrownStrongDoubleIntegrand_le
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ p : ℝ × ℝ, heathBrownStrongDoubleIntegrand delta t p) ≤
      (Real.pi / delta) * heathBrownFullCriticalMoment t := by
  have hfst := integrable_heathBrown_reserve_sq_mul_critical_add hdelta t
  have hsnd := integrable_heathBrown_reserve_sq_snd_mul_critical_add hdelta t
  have hfull := heathBrownFullCriticalMoment_nonneg t
  calc
    (∫ p : ℝ × ℝ, heathBrownStrongDoubleIntegrand delta t p) ≤
        ∫ p : ℝ × ℝ, heathBrownStrongDoubleMajorant delta t p := by
      exact integral_mono
        (integrable_heathBrownStrongDoubleIntegrand hdelta t)
        (integrable_heathBrownStrongDoubleMajorant hdelta t)
        (fun p => heathBrownStrongDoubleIntegrand_le hdelta p)
    _ = (∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ)) *
        heathBrownFullCriticalMoment t := by
      have hEqFst := integral_heathBrown_reserve_sq_mul_critical_add hdelta t
      have hEqSnd := integral_heathBrown_reserve_sq_snd_mul_critical_add hdelta t
      calc
        (∫ p : ℝ × ℝ, heathBrownStrongDoubleMajorant delta t p) =
            ∫ p : ℝ × ℝ, (1 / 2 : ℝ) *
              (heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
                  heathBrownCriticalWeighted t (p.1 + p.2) +
                heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
                  heathBrownCriticalWeighted t (p.1 + p.2)) := by
          apply integral_congr_ae
          filter_upwards with p
          unfold heathBrownStrongDoubleMajorant
          ring
        _ = (1 / 2 : ℝ) * ∫ p : ℝ × ℝ,
              (heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
                  heathBrownCriticalWeighted t (p.1 + p.2) +
                heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
                  heathBrownCriticalWeighted t (p.1 + p.2)) :=
          integral_const_mul _ _
        _ = (1 / 2 : ℝ) *
            ((∫ p : ℝ × ℝ,
                heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
                  heathBrownCriticalWeighted t (p.1 + p.2)) +
              ∫ p : ℝ × ℝ,
                heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
                  heathBrownCriticalWeighted t (p.1 + p.2)) := by
          rw [integral_add hfst hsnd]
        _ = _ := by rw [hEqFst, hEqSnd]; ring
    _ ≤ (Real.pi / delta) * heathBrownFullCriticalMoment t := by
      gcongr
      exact integral_heathBrownGammaReserveKernel_sq_le hdelta

theorem integral_strongKernel_mul_strongMoment_eq_double
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
        heathBrownStrongMellinCriticalMoment delta (t + w)) =
      ∫ p : ℝ × ℝ, heathBrownStrongDoubleIntegrand delta t p := by
  have hdouble := integrable_heathBrownStrongDoubleIntegrand hdelta t
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hdouble ⊢
  rw [integral_prod _ hdouble]
  apply integral_congr_ae
  filter_upwards with w
  unfold heathBrownStrongMellinCriticalMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  unfold heathBrownStrongDoubleIntegrand heathBrownStrongSingularKernel
  ring

theorem integrable_strongKernel_mul_strongMoment
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun w : ℝ => heathBrownStrongSingularKernel delta w *
        heathBrownStrongMellinCriticalMoment delta (t + w)) := by
  have hdouble := integrable_heathBrownStrongDoubleIntegrand hdelta t
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hdouble
  have houter := hdouble.integral_prod_left
  convert houter using 1
  funext w
  unfold heathBrownStrongMellinCriticalMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  unfold heathBrownStrongDoubleIntegrand heathBrownStrongSingularKernel
  ring

/-- The nested equation-(40) moment on a long vertical side has exactly one
factor `delta⁻¹`. -/
theorem integral_strongKernel_mul_strongMoment_le
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
        heathBrownStrongMellinCriticalMoment delta (t + w)) ≤
      (Real.pi / delta) * heathBrownFullCriticalMoment t := by
  rw [integral_strongKernel_mul_strongMoment_eq_double hdelta t]
  exact integral_heathBrownStrongDoubleIntegrand_le hdelta t

end MathCollab.Density.Stronger.PointMean
