module
-- Reversible module-visibility port of the audited development.
/-
Selected actual contour convergence proofs adapted from Scott McColm,
PointMeanMellinVertical.lean and PointMeanContourBasic.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_SHIFT_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local proved Gamma kernel and Abel continuation replace source imports.
-/
public import MathCollab.Density.Stronger.PointMean.FiniteRectangle
public import MathCollab.Density.Stronger.PointMean.GammaKernel
public import MathCollab.Density.AbelZetaGrowth
public import MathCollab.Density.GammaMellin
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour MathCollab.Density.ZetaGrowth
open scoped ComplexOrder
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

theorem exists_heathBrown_Gamma_shift_kernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ v : ℝ), 0 < δ → δ ≤ 1 / 4 →
      (δ + |v|) * ‖Complex.Gamma ((δ : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) ∧
      (δ + |v|) * ‖Complex.Gamma (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) := by
  refine ⟨144, by norm_num, ?_⟩
  intro δ v hδ hδ'
  have h := heathBrown_Gamma_shift_kernel_strong_bound (v := v) hδ (by linarith)
  have he : 144 * Real.exp (-(4 / 3 : ℝ) * |v|) ≤ 144 * Real.exp (-|v|) := by
    gcongr
    linarith [abs_nonneg v]
  exact ⟨h.1.trans he, h.2.trans he⟩

private theorem integrable_Gamma_two_vertical_for_zetaSquare :
    Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) := by
  exact GammaMellin.verticalIntegrable_Gamma (by norm_num : (0 : ℝ) < 2)

theorem ford_norm_eq_re_of_nonneg {z : ℂ} (hz : 0 ≤ z) :
    ‖z‖ = z.re := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hz
  rw [Complex.norm_def, Complex.normSq_apply, ← him]
  rw [zero_mul, add_zero, ← pow_two, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hre]

theorem ford_norm_riemannZeta_le_real
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
      ‖riemannZeta (sigma : ℂ)‖ := by
  let s : ℂ := (sigma : ℂ) + Complex.I * t
  have hs : 1 < s.re := by simp [s, hsigma]
  have hsumS : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs
  have hsumSigma : LSeriesSummable (1 : ℕ → ℂ) (sigma : ℂ) :=
    LSeriesSummable_one_iff.mpr hsigma
  rw [← LSeries_one_eq_riemannZeta hs,
    ← LSeries_one_eq_riemannZeta hsigma, LSeries, LSeries]
  calc
    ‖∑' n, LSeries.term (1 : ℕ → ℂ) s n‖ ≤
        ∑' n, ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
      norm_tsum_le_tsum_norm hsumS.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      apply hsumS.norm.tsum_le_tsum
        (fun n => LSeries.norm_term_le_of_re_le_re
          (1 : ℕ → ℂ) (by simp [s]) n)
        hsumSigma.norm
    _ = ‖∑' n, LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      have hnonneg (n : ℕ) :
          0 ≤ LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n :=
        LSeries.term_nonneg (by norm_num : (0 : ℂ) ≤ 1) sigma
      have hnormTerm (n : ℕ) :
          ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ =
            (LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n).re := by
        exact ford_norm_eq_re_of_nonneg (hnonneg n)
      simp_rw [hnormTerm]
      rw [← Complex.re_tsum hsumSigma]
      exact (ford_norm_eq_re_of_nonneg (tsum_nonneg hnonneg)).symm

theorem continuous_heathBrownZetaSquareMellinIntegrand_vertical
    {s : ℂ} {a : ℝ} (haLower : -(1 : ℝ) < a) (ha0 : a ≠ 0)
    (hpole : s.re + a ≠ 1) :
    Continuous (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        ((a : ℂ) + (v : ℂ) * I)) := by
  apply continuous_iff_continuousAt.2
  intro v
  have hwNoPole : ∀ m : ℕ,
      (a : ℂ) + (v : ℂ) * I ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_self, add_zero, neg_re, natCast_re] at hre
    by_cases hm0 : m = 0
    · subst m
      norm_num at hre
      exact ha0 hre
    · have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
      linarith
  have hGammaAt :=
    (Complex.differentiableAt_Gamma _ hwNoPole).continuousAt
  have hGamma : ContinuousAt
      (fun u : ℝ => Complex.Gamma ((a : ℂ) + (u : ℂ) * I)) v :=
    ContinuousAt.comp (g := Complex.Gamma)
      (f := fun u : ℝ => (a : ℂ) + (u : ℂ) * I)
      hGammaAt (by fun_prop)
  have hzetaPoint : s + ((a : ℂ) + (v : ℂ) * I) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_self, add_zero, one_re] at hre
    exact hpole hre
  have hZetaAt :=
    (differentiableAt_riemannZeta hzetaPoint).continuousAt
  have hZeta : ContinuousAt
      (fun u : ℝ => riemannZeta
        (s + ((a : ℂ) + (u : ℂ) * I))) v :=
    ContinuousAt.comp (g := riemannZeta)
      (f := fun u : ℝ => s + ((a : ℂ) + (u : ℂ) * I))
      hZetaAt (by fun_prop)
  exact hGamma.mul (hZeta.pow 2)

/-- A full-line exponential moment used for the two shifted contours. -/
theorem integrable_abs_sq_mul_exp_neg_abs :
    Integrable (fun v : ℝ => |v| ^ 2 * Real.exp (-|v|)) := by
  have hposRaw : IntegrableOn
      (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1 : ℝ) * x ^ (1 : ℝ)))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (2 : ℝ)) (p := (1 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  have hpos : IntegrableOn
      (fun x : ℝ => |x| ^ 2 * Real.exp (-|x|)) (Ioi 0) := by
    refine hposRaw.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxPos : 0 < x := Set.mem_Ioi.mp hx
    change x ^ (2 : ℝ) * Real.exp (-(1 : ℝ) * x ^ (1 : ℝ)) =
      |x| ^ 2 * Real.exp (-|x|)
    simp [abs_of_pos hxPos, Real.rpow_one]
  have hnegRaw := hpos.comp_neg
  have hneg : IntegrableOn
      (fun x : ℝ => |x| ^ 2 * Real.exp (-|x|)) (Iio 0) := by
    simpa [Set.neg_Ioi, abs_neg] using hnegRaw
  have hleft : IntegrableOn
      (fun x : ℝ => |x| ^ 2 * Real.exp (-|x|)) (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hneg
  have hall := hleft.union hpos
  rw [Iic_union_Ioi] at hall
  exact integrableOn_univ.mp hall

private theorem integrable_heathBrownZetaSquareMellinIntegrand_of_exp
    {s : ℂ} {a G : ℝ}
    (haLower : -(1 : ℝ) < a) (ha0 : a ≠ 0)
    (hsRe : 1 / 4 ≤ s.re + a) (hpole : s.re + a ≠ 1) (hG : 0 ≤ G)
    (hGamma : ∀ v : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        G * Real.exp (-|v|)) :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        ((a : ℂ) + (v : ℂ) * I)) := by
  let f : ℝ → ℂ := fun v =>
    heathBrownZetaSquareMellinIntegrand s
      ((a : ℂ) + (v : ℂ) * I)
  let B : ℝ := |s.re + a| + |s.im| + 2
  let M : ℝ := 100 * G
  let g : ℝ → ℝ := fun v => M * (|v| ^ 2 * Real.exp (-|v|))
  have hBone : 1 ≤ B := by
    dsimp only [B]
    linarith [abs_nonneg (s.re + a), abs_nonneg s.im]
  have hBpos : 0 < B := zero_lt_one.trans_le hBone
  have hCont : Continuous f := by
    simpa [f] using
      continuous_heathBrownZetaSquareMellinIntegrand_vertical
        haLower ha0 hpole
  have hg : Integrable g := integrable_abs_sq_mul_exp_neg_abs.const_mul M
  have hPos : IntegrableOn f (Ioi B) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hvPos : 0 < v := hBpos.trans hv
    have hfar : |s.re + a| + |s.im| + 2 ≤ |v| := by
      rw [abs_of_pos hvPos]
      exact hv.le
    have hheight : 1 ≤ |s.im + v| := by
      have htri := abs_sub_abs_le_abs_sub v (-s.im)
      rw [abs_neg, sub_neg_eq_add] at htri
      rw [add_comm]
      linarith [abs_nonneg (s.re + a)]
    have hzetaRe : (1 / 4 : ℝ) ≤
        (s + ((a : ℂ) + (v : ℂ) * I)).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      exact hsRe
    have hzeta := norm_riemannZeta_le_five_mul_norm hzetaRe
      (by simpa using hheight)
    have hnorm :
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤ 2 * |v| := by
      calc
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤
            |(s + ((a : ℂ) + (v : ℂ) * I)).re| +
              |(s + ((a : ℂ) + (v : ℂ) * I)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |s.re + a| + |s.im + v| := by congr 1 <;> simp
        _ ≤ |s.re + a| + (|s.im| + |v|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |v| := by linarith
    have hzeta' :
        ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ≤
          5 * (2 * |v|) :=
      hzeta.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
    change ‖heathBrownZetaSquareMellinIntegrand s
      ((a : ℂ) + (v : ℂ) * I)‖ ≤ g v
    rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
    dsimp only [g, M]
    calc
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ *
          ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ^ 2 ≤
        (G * Real.exp (-|v|)) * (5 * (2 * |v|)) ^ 2 := by
          exact mul_le_mul (hGamma v)
            (pow_le_pow_left₀ (norm_nonneg _) hzeta' 2)
            (by positivity) (by positivity)
      _ = 100 * G * (|v| ^ 2 * Real.exp (-|v|)) := by ring
  have hNeg : IntegrableOn f (Iio (-B)) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with v hv
    have hvNeg : v < 0 := hv.trans_le (neg_nonpos.mpr hBpos.le)
    have hfar : |s.re + a| + |s.im| + 2 ≤ |v| := by
      rw [abs_of_neg hvNeg]
      change v < -(|s.re + a| + |s.im| + 2) at hv
      linarith
    have hheight : 1 ≤ |s.im + v| := by
      have htri := abs_sub_abs_le_abs_sub v (-s.im)
      rw [abs_neg, sub_neg_eq_add] at htri
      have hlower : |v| - |s.im| ≤ |v + s.im| := htri
      rw [add_comm] at hlower
      linarith [abs_nonneg (s.re + a)]
    have hzetaRe : (1 / 4 : ℝ) ≤
        (s + ((a : ℂ) + (v : ℂ) * I)).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      exact hsRe
    have hzeta := norm_riemannZeta_le_five_mul_norm hzetaRe
      (by simpa using hheight)
    have hnorm :
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤ 2 * |v| := by
      calc
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤
            |(s + ((a : ℂ) + (v : ℂ) * I)).re| +
              |(s + ((a : ℂ) + (v : ℂ) * I)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |s.re + a| + |s.im + v| := by congr 1 <;> simp
        _ ≤ |s.re + a| + (|s.im| + |v|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |v| := by linarith
    have hzeta' :
        ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ≤
          5 * (2 * |v|) :=
      hzeta.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
    change ‖heathBrownZetaSquareMellinIntegrand s
      ((a : ℂ) + (v : ℂ) * I)‖ ≤ g v
    rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
    dsimp only [g, M]
    calc
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ *
          ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ^ 2 ≤
        (G * Real.exp (-|v|)) * (5 * (2 * |v|)) ^ 2 := by
          exact mul_le_mul (hGamma v)
            (pow_le_pow_left₀ (norm_nonneg _) hzeta' 2)
            (by positivity) (by positivity)
      _ = 100 * G * (|v| ^ 2 * Real.exp (-|v|)) := by ring
  have hMid : IntegrableOn f (Icc (-B) B) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : IntegrableOn f (Iic (-B)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hNeg
  have hLeft := hNegClosed.union hMid
  have hLeftSet : Iic (-B) ∪ Icc (-B) B = Iic B := by
    ext v
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hv : v ≤ -B
      · exact Or.inl hv
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeft
  rw [← integrableOn_univ]
  have hAll := hLeft.union hPos
  have hAllSet : Iic B ∪ Ioi B = Set.univ := by
    ext v
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt v B
  rwa [hAllSet] at hAll

theorem integrable_heathBrownZetaSquareMellinIntegrand_plus
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4) (hsRe : 1 / 4 ≤ s.re + delta)
    (hpole : s.re + delta ≠ 1) :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        ((delta : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC, hKernel⟩ := exists_heathBrown_Gamma_shift_kernel_bound
  let G : ℝ := C / delta
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hGamma : ∀ v : ℝ,
      ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ ≤
        G * Real.exp (-|v|) := by
    intro v
    have hk := (hKernel delta v hdelta hdeltaUpper).1
    dsimp only [G]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdelta).2
    calc
      ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ * delta =
          delta * ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ := by ring
      _ ≤
          (delta + |v|) * ‖Complex.Gamma
            ((delta : ℂ) + (v : ℂ) * I)‖ := by
        exact mul_le_mul_of_nonneg_right
          (by linarith [abs_nonneg v]) (norm_nonneg _)
      _ ≤ C * Real.exp (-|v|) := hk
  apply integrable_heathBrownZetaSquareMellinIntegrand_of_exp
    (s := s) (a := delta) (G := G) (by linarith) hdelta.ne'
    hsRe hpole hG hGamma

theorem integrable_heathBrownZetaSquareMellinIntegrand_minus
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4) (hsRe : 1 / 4 ≤ s.re - delta)
    (hpole : s.re - delta ≠ 1) :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        (((-delta : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC, hKernel⟩ := exists_heathBrown_Gamma_shift_kernel_bound
  let G : ℝ := C / delta
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hGamma : ∀ v : ℝ,
      ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        G * Real.exp (-|v|) := by
    intro v
    have hk := (hKernel delta v hdelta hdeltaUpper).2
    dsimp only [G]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdelta).2
    calc
      ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (v : ℂ) * I)‖ * delta =
          delta * ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (v : ℂ) * I)‖ := by ring
      _ ≤
          (delta + |v|) * ‖Complex.Gamma
            (((-delta : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
        exact mul_le_mul_of_nonneg_right
          (by linarith [abs_nonneg v]) (norm_nonneg _)
      _ ≤ C * Real.exp (-|v|) := hk
  apply integrable_heathBrownZetaSquareMellinIntegrand_of_exp
    (s := s) (a := -delta) (G := G) (by linarith) (by linarith)
    (by simpa [sub_eq_add_neg] using hsRe)
    (by simpa [sub_eq_add_neg] using hpole) hG hGamma

theorem integrable_heathBrownZetaSquareMellinIntegrand_right
    {s : ℂ} (hs : 0 ≤ s.re) :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        (((2 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  let Z : ℝ := ‖riemannZeta (((s.re + 2 : ℝ) : ℂ))‖ ^ 2
  let M : ℝ := Z
  have hCont : Continuous (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        (((2 : ℝ) : ℂ) + (v : ℂ) * I)) := by
    apply continuous_heathBrownZetaSquareMellinIntegrand_vertical
    · norm_num
    · norm_num
    · linarith
  have hMajorant : Integrable (fun v : ℝ =>
      M * ‖Complex.Gamma (((2 : ℝ) : ℂ) + (v : ℂ) * I)‖) :=
    integrable_Gamma_two_vertical_for_zetaSquare.norm.const_mul M
  apply hMajorant.mono' hCont.aestronglyMeasurable
  filter_upwards with v
  have hzeta : ‖riemannZeta
      (s + (((2 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        ‖riemannZeta (((s.re + 2 : ℝ) : ℂ))‖ := by
    have hraw := ford_norm_riemannZeta_le_real
      (sigma := s.re + 2) (t := s.im + v) (by linarith)
    have heq : s + (((2 : ℝ) : ℂ) + (v : ℂ) * I) =
        (((s.re + 2 : ℝ) : ℂ) + I * (s.im + v)) := by
      apply Complex.ext <;> simp [mul_comm]
    rw [heq]
    simpa using hraw
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
  change _ ≤ M * _
  dsimp only [M, Z]
  nlinarith [mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hzeta 2)
    (norm_nonneg (Complex.Gamma (((2 : ℝ) : ℂ) + (v : ℂ) * I)))]

end MathCollab.Density.Stronger.PointMean
