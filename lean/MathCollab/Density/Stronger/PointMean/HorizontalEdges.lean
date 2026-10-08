module
-- Reversible module-visibility port of the audited development.
/-
Selected horizontal-edge proofs adapted from Scott McColm,
PointMeanLemmaThreeEdges.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_RECTANGLE_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
Local Abel continuation and the independent explicit Gamma kernel replace
all source growth/Gamma imports. No point-mean or moment premise is used.
-/
public import MathCollab.Density.Stronger.PointMean.FiniteRectangle
public import MathCollab.Density.Stronger.PointMean.GammaKernel
public import MathCollab.Density.AbelZetaGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter
open MathCollab.Density.Contour MathCollab.Density.ZetaGrowth
open scoped Topology Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

theorem eventually_log_sq_le_rpow {q : ℝ} (hq : 0 < q) :
    ∀ᶠ X : ℝ in atTop, (Real.log X) ^ 2 ≤ X ^ q := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ) hq
  filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with X hBound hX
  have hLogNonneg : 0 ≤ Real.log X := Real.log_nonneg hX
  have hXNonneg : 0 ≤ X := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hLogNonneg 2),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hXNonneg q)] at hBound
  simpa [Real.rpow_two] using hBound


theorem eventually_const_mul_rpow_le_rpow
    {D a b : Real} (hab : a < b) :
    ∀ᶠ U : Real in atTop, D * U ^ a <= U ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hTend : Tendsto (fun U : Real => U ^ (b - a)) atTop atTop :=
    tendsto_rpow_atTop hgap
  have hEventually : ∀ᶠ U : Real in atTop, D <= U ^ (b - a) :=
    (tendsto_atTop.1 hTend) D
  filter_upwards [hEventually, eventually_gt_atTop (0 : Real)] with U hU hUpos
  calc
    D * U ^ a <= U ^ (b - a) * U ^ a :=
      mul_le_mul_of_nonneg_right hU (Real.rpow_nonneg hUpos.le _)
    _ = U ^ b := by
      rw [<- Real.rpow_add hUpos]
      congr 1
      ring



theorem eventually_heathBrownLemmaThreeRadius_le_half_identity :
    ∀ᶠ t : ℝ in Filter.atTop,
      heathBrownLemmaThreeRadius t ≤ t / 2 := by
  have hlog := eventually_log_sq_le_rpow (q := (1 / 2 : ℝ)) (by norm_num)
  have hpow := eventually_const_mul_rpow_le_rpow
    (D := (2 : ℝ)) (a := (1 / 2 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  filter_upwards [hlog, hpow, Filter.eventually_gt_atTop (0 : ℝ)] with
      t hlog hpow ht
  unfold heathBrownLemmaThreeRadius
  rw [Real.rpow_one] at hpow
  linarith

theorem exists_norm_Gamma_heathBrown_small_horizontal_strong_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta x R : ℝ),
      0 < delta → delta ≤ 1 / 4 → x ∈ Set.Icc (-delta) delta → 1 ≤ |R| →
      ‖Complex.Gamma ((x : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) := by
  let B : ℝ := 72
  have hStrip (a v : ℝ) (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) :
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        B * Real.exp (-(4 / 3 : ℝ) * |v|) :=
    norm_Gamma_positive_strip_strong ha ha'
  refine ⟨B, by norm_num [B], ?_⟩
  intro delta x R hdelta hdeltaUpper hx hR
  let z : ℂ := (x : ℂ) + (R : ℂ) * I
  have hz : z ≠ 0 := by
    intro hz0
    have him := congrArg Complex.im hz0
    dsimp only [z] at him
    simp at him
    rw [him, abs_zero] at hR
    norm_num at hR
  have hrec := Complex.Gamma_add_one z hz
  have harg : z + 1 = ((1 + x : ℝ) : ℂ) + (R : ℂ) * I := by
    apply Complex.ext
    · simp [z]
      ring
    · simp [z]
  have hshift := hStrip (1 + x) R (by linarith [hx.1])
    (by linarith [hx.2])
  have hnormLower : 1 ≤ ‖z‖ := by
    calc
      1 ≤ |R| := hR
      _ ≤ ‖z‖ := by
        have himz : z.im = R := by simp [z]
        rw [← himz]
        exact Complex.abs_im_le_norm z
  calc
    ‖Complex.Gamma z‖ = 1 * ‖Complex.Gamma z‖ := by ring
    _ ≤ ‖z‖ * ‖Complex.Gamma z‖ := by gcongr
    _ = ‖Complex.Gamma (((1 + x : ℝ) : ℂ) + (R : ℂ) * I)‖ := by
      rw [← harg, hrec, norm_mul]
    _ ≤ B * Real.exp (-(4 / 3 : ℝ) * |R|) := hshift

theorem exists_norm_heathBrownLemmaThree_horizontal_integrand_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t x R : ℝ),
      0 < delta → delta ≤ 1 / 4 → x ∈ Set.Icc (-delta) delta →
      1 ≤ |t + R| → 1 ≤ |R| →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((x : ℝ) : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) := by
  obtain ⟨B, hB, hGamma⟩ :=
    exists_norm_Gamma_heathBrown_small_horizontal_strong_le
  refine ⟨B, hB, ?_⟩
  intro delta t x R hdelta hdeltaUpper hx hheight hR
  have hzetaRe : (1 / 4 : ℝ) ≤
      ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
        (((x : ℝ) : ℂ) + (R : ℂ) * I)).re := by
    simp
    linarith [hx.1]
  have hzeta := norm_riemannZeta_le_five_mul_norm hzetaRe (by simpa using hheight)
  have hnorm :
      ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
        (((x : ℝ) : ℂ) + (R : ℂ) * I)‖ ≤ 1 + |t| + |R| := by
    calc
      ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
          (((x : ℝ) : ℂ) + (R : ℂ) * I)‖ ≤
        |1 / 2 + x| + |t + R| := by
          have h := Complex.norm_le_abs_re_add_abs_im
            ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
              (((x : ℝ) : ℂ) + (R : ℂ) * I))
          simpa using h
      _ ≤ (1 / 2 + |x|) + (|t| + |R|) := by
        gcongr
        · calc
            |1 / 2 + x| ≤ |(1 / 2 : ℝ)| + |x| := abs_add_le _ _
            _ = 1 / 2 + |x| := by norm_num
        · exact abs_add_le _ _
      _ ≤ 1 + |t| + |R| := by
        have hxAbs : |x| ≤ delta := abs_le.mpr hx
        linarith
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
  exact mul_le_mul
    (hGamma delta x R hdelta hdeltaUpper hx hR)
    (pow_le_pow_left₀ (norm_nonneg _) (hzeta.trans
      (mul_le_mul_of_nonneg_left hnorm (by norm_num))) 2)
    (by positivity) (by positivity)

theorem exists_norm_heathBrownLemmaThree_horizontalEdge_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t R : ℝ),
      0 < delta → delta ≤ 1 / 4 → 1 ≤ |t + R| → 1 ≤ |R| →
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) (-delta) delta R‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) := by
  obtain ⟨B, hB, hPoint⟩ :=
    exists_norm_heathBrownLemmaThree_horizontal_integrand_le
  let C : ℝ := B
  refine ⟨C, hB, ?_⟩
  intro delta t R hdelta hdeltaUpper hheight hR
  let F : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let M : ℝ := B * Real.exp (-(4 / 3 : ℝ) * |R|) *
    (5 * (1 + |t| + |R|)) ^ (2 : ℕ)
  have hbase : ‖HIntegral F (-delta) delta R‖ ≤ M * |delta - (-delta)| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (-delta) delta := by
      rw [← Set.uIcc_of_le (by linarith : -delta ≤ delta)]
      exact Set.uIoc_subset_uIcc hx
    simpa only [F, M] using hPoint delta t x R hdelta hdeltaUpper hx' hheight hR
  have hwidth : |delta - (-delta)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    nlinarith [mul_le_mul_of_nonneg_right hpiInv
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖HIntegral F (-delta) delta R‖ ≤
        1 * (M * |delta - (-delta)|) :=
      mul_le_mul hscalar hbase (norm_nonneg _) (by positivity)
    _ ≤ M := by nlinarith [mul_le_mul_of_nonneg_left hwidth hM]
    _ = C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) := by rfl

theorem heathBrown_logSquare_exponential_absorption
    {D t : ℝ} (ht : 0 < t) (hDt : D ≤ t)
    (hlog : 9 / 4 ≤ Real.log t) :
    D * t ^ (2 : ℕ) *
      Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) ≤ 1 := by
  let L : ℝ := Real.log t
  have hlog' : 9 / 4 ≤ L := by simpa only [L] using hlog
  have htEq : t = Real.exp L := by
    dsimp only [L]
    exact (Real.exp_log ht).symm
  have hpow : D * t ^ (2 : ℕ) ≤ t * t ^ (2 : ℕ) := by gcongr
  calc
    D * t ^ (2 : ℕ) *
        Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) ≤
      (t * t ^ (2 : ℕ)) *
        Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) := by gcongr
    _ = Real.exp (3 * L - (4 / 3 : ℝ) * L ^ (2 : ℕ)) := by
      change (t * t ^ (2 : ℕ)) *
        Real.exp (-(4 / 3 : ℝ) * L ^ (2 : ℕ)) = _
      rw [htEq, pow_two]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (L - 9 / 8)]
    _ = 1 := Real.exp_zero

theorem eventually_norm_heathBrownLemmaThree_horizontalEdges_le_one :
    ∀ᶠ t : ℝ in Filter.atTop,
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (-heathBrownLemmaThreeRadius t)‖ ≤ 1 ∧
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (heathBrownLemmaThreeRadius t)‖ ≤ 1 := by
  obtain ⟨B, hB, hHorizontal⟩ :=
    exists_norm_heathBrownLemmaThree_horizontalEdge_le
  have hLog := Real.tendsto_log_atTop.eventually
    (Filter.eventually_ge_atTop (4 : ℝ))
  filter_upwards [eventually_heathBrownLemmaThreeRadius_le_half_identity,
    hLog, Filter.eventually_ge_atTop (max 2 (100 * B))] with
      t hRadius hlog htLarge
  have htTwo : 2 ≤ t := (le_max_left _ _).trans htLarge
  have hBt : 100 * B ≤ t := (le_max_right _ _).trans htLarge
  have ht : 0 < t := by linarith
  have hdelta : 0 < heathBrownLemmaThreeDelta t := by
    unfold heathBrownLemmaThreeDelta
    have : 0 < Real.log t := by linarith
    positivity
  have hdeltaUpper : heathBrownLemmaThreeDelta t ≤ 1 / 4 := by
    unfold heathBrownLemmaThreeDelta
    exact one_div_le_one_div_of_le (by norm_num) hlog
  have hH : 1 ≤ heathBrownLemmaThreeRadius t := by
    unfold heathBrownLemmaThreeRadius
    nlinarith
  have hHNonneg : 0 ≤ heathBrownLemmaThreeRadius t := by linarith
  have hminusHeight : 1 ≤ |t - heathBrownLemmaThreeRadius t| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hplusHeight : 1 ≤ |t + heathBrownLemmaThreeRadius t| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hSize :
      5 * (1 + |t| + |heathBrownLemmaThreeRadius t|) ≤ 10 * t := by
    rw [abs_of_pos ht, abs_of_nonneg hHNonneg]
    nlinarith
  have hAbsorb := heathBrown_logSquare_exponential_absorption
    (D := 100 * B) ht hBt (by linarith)
  constructor
  · have hraw := hHorizontal (heathBrownLemmaThreeDelta t) t
      (-heathBrownLemmaThreeRadius t) hdelta hdeltaUpper
      (by simpa only [sub_eq_add_neg] using hminusHeight)
      (by simpa only [abs_neg, abs_of_nonneg hHNonneg] using hH)
    calc
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (-heathBrownLemmaThreeRadius t)‖ ≤
        B * Real.exp (-(4 / 3 : ℝ) * |(-heathBrownLemmaThreeRadius t)|) *
          (5 * (1 + |t| + |(-heathBrownLemmaThreeRadius t)|)) ^
            (2 : ℕ) := hraw
      _ ≤ B * Real.exp (-(4 / 3 : ℝ) * heathBrownLemmaThreeRadius t) *
          (10 * t) ^ (2 : ℕ) := by
        rw [abs_neg, abs_of_nonneg hHNonneg]
        have hSize' :
            5 * (1 + |t| + heathBrownLemmaThreeRadius t) ≤ 10 * t := by
          simpa only [abs_of_nonneg hHNonneg] using hSize
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hSize' 2) (by positivity)
      _ = (100 * B) * t ^ (2 : ℕ) *
          Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) := by
        unfold heathBrownLemmaThreeRadius
        ring
      _ ≤ 1 := hAbsorb
  · have hraw := hHorizontal (heathBrownLemmaThreeDelta t) t
      (heathBrownLemmaThreeRadius t) hdelta hdeltaUpper hplusHeight
      (by simpa only [abs_of_nonneg hHNonneg] using hH)
    calc
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (heathBrownLemmaThreeRadius t)‖ ≤
        B * Real.exp (-(4 / 3 : ℝ) * |heathBrownLemmaThreeRadius t|) *
          (5 * (1 + |t| + |heathBrownLemmaThreeRadius t|)) ^
            (2 : ℕ) := hraw
      _ ≤ B * Real.exp (-(4 / 3 : ℝ) * heathBrownLemmaThreeRadius t) *
          (10 * t) ^ (2 : ℕ) := by
        rw [abs_of_nonneg hHNonneg]
        have hSize' :
            5 * (1 + |t| + heathBrownLemmaThreeRadius t) ≤ 10 * t := by
          simpa only [abs_of_nonneg hHNonneg] using hSize
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hSize' 2) (by positivity)
      _ = (100 * B) * t ^ (2 : ℕ) *
          Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) := by
        unfold heathBrownLemmaThreeRadius
        ring
      _ ≤ 1 := hAbsorb


end MathCollab.Density.Stronger.PointMean
