module
-- Reversible module-visibility port of the audited development.
/-
Selected horizontal-limit proofs adapted from Scott McColm,
PointMeanMellinHorizontal.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_SHIFT_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The wide-strip Gamma bound is proved directly by three recurrences;
local Abel growth replaces the source growth import.
-/
public import MathCollab.Density.Stronger.PointMean.FiniteRectangle
public import MathCollab.Density.AbelZetaGrowth
public import MathCollab.Density.GammaMellin
public import Mathlib.Analysis.Real.Pi.Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour MathCollab.Density.ZetaGrowth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

theorem heathBrown_Gamma_wide_strip_decay
    {a t : ℝ} (haLower : -(1 / 4 : ℝ) ≤ a) (haUpper : a ≤ 2) :
    |t| ^ 3 * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 := by
  by_cases ht : t = 0
  · subst t
    norm_num
  let z : ℂ := (a : ℂ) + (t : ℂ) * I
  have hz (j : ℝ) : z + (j : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [z] at hi
    exact ht hi
  have hrec : Complex.Gamma (z + 3) =
      (z + 2) * (z + 1) * z * Complex.Gamma z := by
    rw [show z + 3 = (z + 2) + 1 by ring,
      Complex.Gamma_add_one (z + 2) (by simpa using hz 2),
      show z + 2 = (z + 1) + 1 by ring,
      Complex.Gamma_add_one (z + 1) (by simpa using hz 1),
      Complex.Gamma_add_one z (by simpa using hz 0)]
    ring
  have hcoord (j : ℝ) : |t| ≤ ‖z + (j : ℂ)‖ := by
    simpa [z] using Complex.abs_im_le_norm (z + (j : ℂ))
  have hprod : |t| ^ 3 ≤ ‖z + 2‖ * ‖z + 1‖ * ‖z‖ := by
    calc
      |t| ^ 3 = |t| * |t| * |t| := by ring
      _ ≤ ‖z + 2‖ * ‖z + 1‖ * ‖z‖ := by
        gcongr
        · simpa using hcoord 2
        · simpa using hcoord 1
        · simpa using hcoord 0
  have hnorm : ‖Complex.Gamma (z + 3)‖ ≤ Real.Gamma (a + 3) := by
    simpa [z] using GammaMellin.norm_Gamma_le_realGamma_re
      (s := z + 3) (by simp [z]; linarith)
  have hreal : Real.Gamma (a + 3) ≤ Real.Gamma 5 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by change (2 : ℝ) ≤ a + 3; linarith) (by norm_num) (by linarith)
  have hfive : Real.Gamma 5 = 24 := by
    convert Real.Gamma_nat_eq_factorial 4 using 1 <;> norm_num
  calc
    _ ≤ (‖z + 2‖ * ‖z + 1‖ * ‖z‖) * ‖Complex.Gamma z‖ :=
      mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖Complex.Gamma (z + 3)‖ := by rw [hrec]; simp only [norm_mul]
    _ ≤ 24 := hnorm.trans (hreal.trans_eq hfive)

theorem heathBrown_Gamma_wide_strip_norm_le
    {a t : ℝ} (haLower : -(1 / 4 : ℝ) ≤ a) (haUpper : a ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 / |t| ^ 3 := by
  have htPos : 0 < |t| := zero_lt_one.trans_le ht
  apply (le_div_iff₀ (pow_pos htPos 3)).2
  simpa [mul_comm] using heathBrown_Gamma_wide_strip_decay haLower haUpper

noncomputable def heathBrownMellinHorizontalSize (s : ℂ) (R : ℝ) : ℝ :=
  |s.re| + 2 + |s.im| + |R|

theorem norm_heathBrownZetaSquareMellinIntegrand_horizontal_le
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {x R : ℝ} (hxLower : -(1 / 4 : ℝ) ≤ x) (hxUpper : x ≤ 2)
    (hR : 1 ≤ |R|) (hheight : 1 ≤ |s.im + R|) :
    ‖heathBrownZetaSquareMellinIntegrand s
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      (24 / |R| ^ 3) *
        (5 * heathBrownMellinHorizontalSize s R) ^ 2 := by
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
  have hGamma := heathBrown_Gamma_wide_strip_norm_le hxLower hxUpper hR
  have hzetaRe : (1 / 4 : ℝ) ≤
      (s + ((x : ℂ) + (R : ℂ) * I)).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    linarith
  have hzetaIm : 1 ≤ |(s + ((x : ℂ) + (R : ℂ) * I)).im| := by
    simpa using hheight
  have hzeta := norm_riemannZeta_le_five_mul_norm hzetaRe hzetaIm
  have hnorm :
      ‖s + ((x : ℂ) + (R : ℂ) * I)‖ ≤
        heathBrownMellinHorizontalSize s R := by
    calc
      ‖s + ((x : ℂ) + (R : ℂ) * I)‖ ≤
          |(s + ((x : ℂ) + (R : ℂ) * I)).re| +
            |(s + ((x : ℂ) + (R : ℂ) * I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re + x| + |s.im + R| := by congr 1 <;> simp
      _ ≤ (|s.re| + |x|) + (|s.im| + |R|) := by
        gcongr <;> exact abs_add_le _ _
      _ ≤ (|s.re| + 2) + (|s.im| + |R|) := by
        gcongr
        exact (abs_le.mpr ⟨by linarith, hxUpper⟩)
      _ = heathBrownMellinHorizontalSize s R := by
        simp only [heathBrownMellinHorizontalSize]
        ring
  have hzeta' : ‖riemannZeta
      (s + ((x : ℂ) + (R : ℂ) * I))‖ ≤
        5 * heathBrownMellinHorizontalSize s R :=
    hzeta.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
  exact mul_le_mul hGamma (pow_le_pow_left₀ (norm_nonneg _) hzeta' 2)
    (by positivity) (by positivity)

theorem norm_heathBrownMellin_HIntegral'_le
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {a b R : ℝ} (ha : -(1 / 4 : ℝ) ≤ a) (hb : b ≤ 2) (hab : a ≤ b)
    (hR : 1 ≤ |R|) (hheight : 1 ≤ |s.im + R|) :
    ‖HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b R‖ ≤
      (9 / 4 : ℝ) * ((24 / |R| ^ 3) *
        (5 * heathBrownMellinHorizontalSize s R) ^ 2) := by
  let M : ℝ := (24 / |R| ^ 3) *
    (5 * heathBrownMellinHorizontalSize s R) ^ 2
  have hbase :
      ‖HIntegral (heathBrownZetaSquareMellinIntegrand s) a b R‖ ≤
        M * |b - a| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      rw [← Set.uIcc_of_le hab]
      exact Set.uIoc_subset_uIcc hx
    exact norm_heathBrownZetaSquareMellinIntegrand_horizontal_le
      hsLower (ha.trans hx'.1) (hx'.2.trans hb) hR hheight
  have hwidth : |b - a| ≤ 9 / 4 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
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
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖HIntegral (heathBrownZetaSquareMellinIntegrand s) a b R‖ ≤
      1 * (M * |b - a|) :=
        mul_le_mul hscalar hbase (norm_nonneg _) (by positivity)
    _ ≤ (9 / 4 : ℝ) * M := by
      nlinarith [mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ M)]
    _ = _ := by rfl

theorem tendsto_heathBrownMellin_HIntegral'_zero
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {a b : ℝ} (ha : -(1 / 4 : ℝ) ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
    Tendsto (fun R : ℝ =>
      HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b R)
      atTop (nhds 0) := by
  let D : ℝ := |s.re| + 2 + |s.im|
  let C : ℝ := (9 / 4 : ℝ) * 24 * (5 * 2) ^ 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun R : ℝ => C * R⁻¹)
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (max 1 (max D (|s.im| + 1)))] with R hR
    have hRone : 1 ≤ R := (le_max_left _ _).trans hR
    have hDR : D ≤ R := (le_max_left D (|s.im| + 1)).trans
      ((le_max_right 1 _).trans hR)
    have hHeightR : |s.im| + 1 ≤ R :=
      (le_max_right D (|s.im| + 1)).trans ((le_max_right 1 _).trans hR)
    have hRpos : 0 < R := zero_lt_one.trans_le hRone
    have hheight : 1 ≤ |s.im + R| := by
      rw [abs_of_nonneg (by linarith [neg_abs_le s.im])]
      linarith [neg_abs_le s.im]
    have hsize : heathBrownMellinHorizontalSize s R ≤ 2 * R := by
      unfold heathBrownMellinHorizontalSize
      rw [abs_of_pos hRpos]
      dsimp only [D] at hDR
      linarith
    have hsizeNonneg : 0 ≤ heathBrownMellinHorizontalSize s R := by
      unfold heathBrownMellinHorizontalSize
      positivity
    have hraw := norm_heathBrownMellin_HIntegral'_le
      hsLower ha hb hab (R := R) (by simpa [abs_of_pos hRpos] using hRone) hheight
    calc
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b R‖ ≤
          (9 / 4 : ℝ) * ((24 / |R| ^ 3) *
            (5 * heathBrownMellinHorizontalSize s R) ^ 2) := hraw
      _ ≤ (9 / 4 : ℝ) * ((24 / R ^ 3) * (5 * (2 * R)) ^ 2) := by
        rw [abs_of_pos hRpos]
        gcongr
      _ = C * R⁻¹ := by
        dsimp only [C]
        field_simp
  · simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
      Tendsto (fun R : ℝ => C * R⁻¹) atTop (nhds (C * 0)))

theorem tendsto_heathBrownMellin_HIntegral'_neg_zero
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {a b : ℝ} (ha : -(1 / 4 : ℝ) ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
    Tendsto (fun R : ℝ =>
      HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b (-R))
      atTop (nhds 0) := by
  let D : ℝ := |s.re| + 2 + |s.im|
  let C : ℝ := (9 / 4 : ℝ) * 24 * (5 * 2) ^ 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun R : ℝ => C * R⁻¹)
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (max 1 (max D (|s.im| + 1)))] with R hR
    have hRone : 1 ≤ R := (le_max_left _ _).trans hR
    have hDR : D ≤ R := (le_max_left D (|s.im| + 1)).trans
      ((le_max_right 1 _).trans hR)
    have hHeightR : |s.im| + 1 ≤ R :=
      (le_max_right D (|s.im| + 1)).trans ((le_max_right 1 _).trans hR)
    have hRpos : 0 < R := zero_lt_one.trans_le hRone
    have hheight : 1 ≤ |s.im - R| := by
      have habsRaw := abs_sub_abs_le_abs_sub R s.im
      rw [abs_of_pos hRpos] at habsRaw
      have habs : R - |s.im| ≤ |s.im - R| := by
        rw [abs_sub_comm]
        linarith
      linarith
    have hsize : heathBrownMellinHorizontalSize s (-R) ≤ 2 * R := by
      unfold heathBrownMellinHorizontalSize
      rw [abs_neg, abs_of_pos hRpos]
      dsimp only [D] at hDR
      linarith
    have hsizeNonneg : 0 ≤ heathBrownMellinHorizontalSize s (-R) := by
      unfold heathBrownMellinHorizontalSize
      positivity
    have hraw := norm_heathBrownMellin_HIntegral'_le
      hsLower ha hb hab (R := -R)
      (by simpa [abs_neg, abs_of_pos hRpos] using hRone)
      (by simpa [sub_eq_add_neg] using hheight)
    calc
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b (-R)‖ ≤
          (9 / 4 : ℝ) * ((24 / |-R| ^ 3) *
            (5 * heathBrownMellinHorizontalSize s (-R)) ^ 2) := hraw
      _ ≤ (9 / 4 : ℝ) * ((24 / R ^ 3) * (5 * (2 * R)) ^ 2) := by
        rw [abs_neg, abs_of_pos hRpos]
        gcongr
      _ = C * R⁻¹ := by
        dsimp only [C]
        field_simp
  · simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
      Tendsto (fun R : ℝ => C * R⁻¹) atTop (nhds (C * 0)))

end MathCollab.Density.Stronger.PointMean
