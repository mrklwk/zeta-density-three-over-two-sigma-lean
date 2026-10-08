module
-- Reversible module-visibility port of the audited development.
/-
Selected exponential-critical-moment convergence proofs adapted from Scott
McColm, PointMeanOffCritical.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The critical norm is the repository's literal actual-zeta norm.
-/
public import MathCollab.Density.Stronger.PointMean.MellinVertical
public import MathCollab.Density.Stronger.CriticalMoment

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open MathCollab.Density.ZetaGrowth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The exact weighted critical-line moment produced by the shifted Gamma
kernel. -/
noncomputable def heathBrownMellinCriticalMoment (delta t : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-|u|) / (delta + |u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

/-- The untruncated exponential convolution occurring after the source choice
`delta = (log t)⁻¹`. -/
noncomputable def heathBrownFullCriticalMoment (t : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-|u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

private theorem heathBrownMellinCriticalMoment_integrand_nonneg
    {delta t u : ℝ} (hdelta : 0 < delta) :
    0 ≤ Real.exp (-|u|) / (delta + |u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) := by
  positivity

/-- Absolute convergence of the exact weighted critical-line moment. -/
theorem integrable_heathBrownMellinCriticalMoment
    {delta t : ℝ} (hdelta : 0 < delta) :
    Integrable (fun u : ℝ => Real.exp (-|u|) / (delta + |u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-|u|) / (delta + |u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)
  let B : ℝ := |t| + 2
  let M : ℝ := 100 / delta
  let g : ℝ → ℝ := fun u => M * (|u| ^ 2 * Real.exp (-|u|))
  have hBpos : 0 < B := by
    dsimp only [B]
    linarith [abs_nonneg t]
  have hMnonneg : 0 ≤ M := by dsimp only [M]; positivity
  have hCont : Continuous f := by
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro u hu
        have : 0 < delta + |u| := by positivity
        exact this.ne' hu
    · exact (continuous_zetaMomentCriticalNorm.pow 2).comp (by fun_prop)
  have hg : Integrable g :=
    integrable_abs_sq_mul_exp_neg_abs.const_mul M
  have hTail : ∀ u : ℝ, B < |u| → ‖f u‖ ≤ g u := by
    intro u hu
    have hheight : 1 ≤ |t + u| := by
      have htri := abs_sub_abs_le_abs_sub u (-t)
      rw [abs_neg, sub_neg_eq_add] at htri
      rw [add_comm] at htri
      linarith
    let z : ℂ := ((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
    have hzRe : (1 / 4 : ℝ) ≤ z.re := by
      simp [z]
      norm_num
    have hzeta := norm_riemannZeta_le_five_mul_norm hzRe
      (by simpa [z] using hheight)
    have hnorm : ‖z‖ ≤ 2 * |u| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (1 / 2 : ℝ) + |t + u| := by simp [z]
        _ ≤ 1 / 2 + (|t| + |u|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |u| := by linarith
    have hzeta' : zetaMomentCriticalNorm (t + u) ≤ 10 * |u| := by
      unfold zetaMomentCriticalNorm
      change ‖riemannZeta z‖ ≤ _
      exact hzeta.trans (by nlinarith)
    have hdenom : delta ≤ delta + |u| := by linarith [abs_nonneg u]
    have hrecip : 1 / (delta + |u|) ≤ 1 / delta := by
      exact one_div_le_one_div_of_le hdelta hdenom
    have hsq : zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
        100 * |u| ^ 2 := by
      calc
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
            (10 * |u|) ^ (2 : ℕ) :=
          pow_le_pow_left₀
            (norm_nonneg (riemannZeta
              (((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I))) hzeta' 2
        _ = 100 * |u| ^ 2 := by ring
    have hfNonneg : 0 ≤ f u := by
      dsimp only [f]
      exact heathBrownMellinCriticalMoment_integrand_nonneg hdelta
    rw [Real.norm_eq_abs, abs_of_nonneg hfNonneg]
    dsimp only [f, g, M]
    have hexp : 0 ≤ Real.exp (-|u|) := (Real.exp_pos _).le
    calc
      Real.exp (-|u|) / (delta + |u|) *
          zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
        (Real.exp (-|u|) / delta) * (100 * |u| ^ 2) := by
          gcongr
      _ = 100 / delta * (|u| ^ 2 * Real.exp (-|u|)) := by ring
  have hPos : IntegrableOn f (Ioi B) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hTail u (by rw [abs_of_pos (hBpos.trans hu)]; exact hu)
  have hNeg : IntegrableOn f (Iio (-B)) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    have hu' : u < -B := Set.mem_Iio.mp hu
    have huNeg : u < 0 := hu'.trans_le (neg_nonpos.mpr hBpos.le)
    apply hTail u
    rw [abs_of_neg huNeg]
    linarith
  have hMid : IntegrableOn f (Icc (-B) B) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : IntegrableOn f (Iic (-B)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hNeg
  have hLeft := hNegClosed.union hMid
  have hLeftSet : Iic (-B) ∪ Icc (-B) B = Iic B := by
    ext u
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hu : u ≤ -B
      · exact Or.inl hu
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeft
  rw [← integrableOn_univ]
  have hAll := hLeft.union hPos
  have hAllSet : Iic B ∪ Ioi B = Set.univ := by
    ext u
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt u B
  rwa [hAllSet] at hAll

/-- Absolute convergence of Heath--Brown's full exponential convolution. -/
theorem integrable_heathBrownFullCriticalMoment (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-|u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-|u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)
  let B : ℝ := |t| + 2
  let g : ℝ → ℝ := fun u => 100 * (|u| ^ 2 * Real.exp (-|u|))
  have hBpos : 0 < B := by
    dsimp only [B]
    linarith [abs_nonneg t]
  have hCont : Continuous f := by
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-|u|))).mul
      ((continuous_zetaMomentCriticalNorm.pow 2).comp (by fun_prop))
  have hg : Integrable g :=
    integrable_abs_sq_mul_exp_neg_abs.const_mul 100
  have hTail : ∀ u : ℝ, B < |u| → ‖f u‖ ≤ g u := by
    intro u hu
    have hheight : 1 ≤ |t + u| := by
      have htri := abs_sub_abs_le_abs_sub u (-t)
      rw [abs_neg, sub_neg_eq_add, add_comm] at htri
      linarith
    let z : ℂ := ((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
    have hzRe : (1 / 4 : ℝ) ≤ z.re := by
      simp [z]
      norm_num
    have hzeta := norm_riemannZeta_le_five_mul_norm hzRe
      (by simpa [z] using hheight)
    have hnorm : ‖z‖ ≤ 2 * |u| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (1 / 2 : ℝ) + |t + u| := by simp [z]
        _ ≤ 1 / 2 + (|t| + |u|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |u| := by linarith
    have hzeta' : zetaMomentCriticalNorm (t + u) ≤ 10 * |u| := by
      unfold zetaMomentCriticalNorm
      change ‖riemannZeta z‖ ≤ _
      exact hzeta.trans (by nlinarith)
    have hsq : zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
        100 * |u| ^ 2 := by
      calc
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
            (10 * |u|) ^ (2 : ℕ) :=
          pow_le_pow_left₀
            (norm_nonneg (riemannZeta
              (((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I))) hzeta' 2
        _ = 100 * |u| ^ 2 := by ring
    have hfNonneg : 0 ≤ f u := by dsimp only [f]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hfNonneg]
    dsimp only [f, g]
    calc
      Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
          Real.exp (-|u|) * (100 * |u| ^ 2) := by gcongr
      _ = 100 * (|u| ^ 2 * Real.exp (-|u|)) := by ring
  have hPos : IntegrableOn f (Ioi B) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hTail u (by rw [abs_of_pos (hBpos.trans hu)]; exact hu)
  have hNeg : IntegrableOn f (Iio (-B)) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    have hu' : u < -B := Set.mem_Iio.mp hu
    have huNeg : u < 0 := hu'.trans_le (neg_nonpos.mpr hBpos.le)
    apply hTail u
    rw [abs_of_neg huNeg]
    linarith
  have hMid : IntegrableOn f (Icc (-B) B) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : IntegrableOn f (Iic (-B)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hNeg
  have hLeft := hNegClosed.union hMid
  have hLeftSet : Iic (-B) ∪ Icc (-B) B = Iic B := by
    ext u
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hu : u ≤ -B
      · exact Or.inl hu
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeft
  rw [← integrableOn_univ]
  have hAll := hLeft.union hPos
  have hAllSet : Iic B ∪ Ioi B = Set.univ := by
    ext u
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt u B
  rwa [hAllSet] at hAll

/-- The exact Gamma-kernel moment loses at most `delta⁻¹` against the
unweighted exponential convolution. -/
theorem heathBrownMellinCriticalMoment_le_full
    {delta t : ℝ} (hdelta : 0 < delta) :
    heathBrownMellinCriticalMoment delta t ≤
      (1 / delta) * heathBrownFullCriticalMoment t := by
  unfold heathBrownMellinCriticalMoment heathBrownFullCriticalMoment
  calc
    (∫ u : ℝ, Real.exp (-|u|) / (delta + |u|) *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) ≤
      ∫ u : ℝ, (1 / delta) * (Real.exp (-|u|) *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
          apply integral_mono
            (integrable_heathBrownMellinCriticalMoment
              (delta := delta) (t := t) hdelta)
            ((integrable_heathBrownFullCriticalMoment t).const_mul (1 / delta))
          intro u
          have hdenom : delta ≤ delta + |u| := by
            linarith [abs_nonneg u]
          have hrecip : 1 / (delta + |u|) ≤ 1 / delta :=
            one_div_le_one_div_of_le hdelta hdenom
          change Real.exp (-|u|) / (delta + |u|) *
              zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
            (1 / delta) * (Real.exp (-|u|) *
              zetaMomentCriticalNorm (t + u) ^ (2 : ℕ))
          calc
            Real.exp (-|u|) / (delta + |u|) *
                zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) =
              (1 / (delta + |u|)) * (Real.exp (-|u|) *
                zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by ring
            _ ≤ (1 / delta) * (Real.exp (-|u|) *
                zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
              gcongr
    _ = (1 / delta) * ∫ u : ℝ, Real.exp (-|u|) *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) :=
      integral_const_mul _ _

theorem heathBrownMellinCriticalMoment_nonneg
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 ≤ heathBrownMellinCriticalMoment delta t := by
  unfold heathBrownMellinCriticalMoment
  exact integral_nonneg fun u =>
    heathBrownMellinCriticalMoment_integrand_nonneg hdelta

theorem heathBrownFullCriticalMoment_nonneg (t : ℝ) :
    0 ≤ heathBrownFullCriticalMoment t := by
  unfold heathBrownFullCriticalMoment
  exact integral_nonneg fun u => by positivity


end MathCollab.Density.Stronger.PointMean
