module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightKernel

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem zetaDivisorWeight_finiteRectangle (q : ℂ) {H : ℝ} (hH : 0 < H) :
    RectangleIntegral' (zetaDivisorWeightKernel q)
      ((-1 : ℂ) - (H : ℂ) * I) ((1 : ℂ) + (H : ℂ) * I) = 1 := by
  change RectangleIntegral' (fun u => zetaDivisorWeightNumerator q u / u) _ _ = 1
  let F := zetaDivisorWeightNumerator q
  let z : ℂ := -1 - (H : ℂ) * I
  let w : ℂ := 1 + (H : ℂ) * I
  have hzero : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      uIoo_of_le (by simp [z, w] : z.re ≤ w.re),
      uIoo_of_le (by simp [z, w]; linarith : z.im ≤ w.im)]
    simp [z, w, hH]
  have hdslope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    rw [differentiableOn_dslope hzero]
    exact (differentiable_zetaDivisorWeightNumerator q).differentiableOn
  have hprincipal : Set.EqOn
      ((fun u : ℂ => F u / u) - fun u => F 0 / (u - 0))
      (dslope F 0) (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    rw [Pi.sub_apply, dslope_of_ne F hu0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp
  have h := ResidueTheoremOnRectangleWithSimplePole
    (f := fun u : ℂ => F u / u) (g := dslope F 0) (p := 0) (A := F 0)
    (zRe_le_wRe := by simp [z, w]) (zIm_le_wIm := by simp [z, w]; linarith)
    hzero hdslope hprincipal
  simpa only [F, z, w, zetaDivisorWeightNumerator_zero] using h

theorem norm_zetaDivisorWeightKernel_horizontal_le (q : ℂ)
    {H x : ℝ} (hH : 1 ≤ H) (hx : |x| ≤ 1) :
    ‖zetaDivisorWeightKernel q ((x : ℂ) + (H : ℂ) * I)‖ ≤
      (625 * Real.exp (100 + |q.re| + q.im ^ 2 / 2)) *
        Real.exp (-99 * H ^ 2) * (2 + H) ^ 8 := by
  let w : ℂ := (x : ℂ) + (H : ℂ) * I
  have hH0 : 0 ≤ H := by linarith
  have hw : ‖w‖ ≤ 2 + H := by
    have h := norm_add_le (x : ℂ) ((H : ℂ) * I)
    simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hH0] at h
    dsimp [w]
    linarith
  have haux := norm_hughesYoungAuxiliaryZero_le_polynomial (show 1 ≤ 2 + H by linarith) hw
  have hwl : 1 ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    simp only [w, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add, abs_of_nonneg hH0] at h
    linarith
  have hxsq : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hqx : -q.re * x ≤ |q.re| := by
    calc
      _ ≤ |-q.re * x| := le_abs_self _
      _ = |q.re| * |x| := by rw [abs_mul, abs_neg]
      _ ≤ _ := by nlinarith [abs_nonneg q.re]
  have he : (100 * w ^ 2).re + (-q * w).re ≤
      (100 + |q.re| + q.im ^ 2 / 2) - 99 * H ^ 2 := by
    norm_num [w, pow_two, mul_re, mul_im]
    nlinarith [sq_nonneg (q.im - H)]
  change ‖zetaDivisorWeightNumerator q w / w‖ ≤ _
  rw [zetaDivisorWeightNumerator, norm_div, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp]
  calc
    _ = (Real.exp ((100 * w ^ 2).re + (-q * w).re) * ‖hughesYoungAuxiliaryZero w‖) / ‖w‖ := by
      rw [Real.exp_add]
      ring
    _ ≤ (Real.exp ((100 + |q.re| + q.im ^ 2 / 2) - 99 * H ^ 2) *
        (625 * (2 + H) ^ 8)) / 1 := by
      gcongr
    _ = _ := by
      rw [show (100 + |q.re| + q.im ^ 2 / 2) - 99 * H ^ 2 =
        (100 + |q.re| + q.im ^ 2 / 2) + (-99 * H ^ 2) by ring, Real.exp_add]
      ring

theorem tendsto_zetaDivisorWeight_horizontal_zero (q : ℂ) :
    Tendsto (fun H : ℝ => HIntegral' (zetaDivisorWeightKernel q) (-1) 1 H) atTop (𝓝 0) := by
  let C : ℝ := 625 * Real.exp (100 + |q.re| + q.im ^ 2 / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hExp : Tendsto (fun H : ℝ => Real.exp (-(1 / 2 : ℝ) * H)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0))
  have hbase : Tendsto (fun H : ℝ => H ^ 8 * Real.exp (-99 * H ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 99) (8 : ℕ)).tendsto_zero_of_tendsto
        hExp
  have htop : Tendsto (fun H : ℝ => HIntegral (zetaDivisorWeightKernel q) (-1) 1 H)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (show ∀ᶠ H : ℝ in atTop,
        ‖HIntegral (zetaDivisorWeightKernel q) (-1) 1 H‖ ≤
          (512 * C) * (H ^ 8 * Real.exp (-99 * H ^ 2)) by
        filter_upwards [eventually_ge_atTop (2 : ℝ)] with H hH
        have hi : ‖HIntegral (zetaDivisorWeightKernel q) (-1) 1 H‖ ≤
            (C * Real.exp (-99 * H ^ 2) * (2 + H) ^ 8) * 2 := by
          unfold HIntegral
          have hpoint (x : ℝ) (hx : x ∈ uIoc (-1 : ℝ) 1) :
              ‖zetaDivisorWeightKernel q ((x : ℂ) + (H : ℂ) * I)‖ ≤
                C * Real.exp (-99 * H ^ 2) * (2 + H) ^ 8 := by
            have hx' : x ∈ Icc (-1 : ℝ) 1 := by
              simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx
            exact norm_zetaDivisorWeightKernel_horizontal_le q (by linarith) (abs_le.mpr hx')
          convert intervalIntegral.norm_integral_le_of_norm_le_const hpoint using 1
          norm_num
        have hp : (2 + H) ^ 8 ≤ 256 * H ^ 8 := by
          calc
            _ ≤ (2 * H) ^ 8 := by
              gcongr
              linarith
            _ = _ := by ring
        apply hi.trans
        nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ C * Real.exp (-99 * H ^ 2) by positivity)])
    simpa only [mul_zero] using hbase.const_mul (512 * C)
  unfold HIntegral'
  simpa using htop.const_smul (1 / (2 * Real.pi * I))

theorem hIntegral_zetaDivisorWeight_bottom (q : ℂ) (H : ℝ) :
    HIntegral (zetaDivisorWeightKernel q) (-1) 1 (-H) =
      -HIntegral (zetaDivisorWeightKernel (-q)) (-1) 1 H := by
  have hpoint (x : ℝ) :
      zetaDivisorWeightKernel q ((x : ℂ) + (-H : ℂ) * I) =
        -zetaDivisorWeightKernel (-q) (((-x : ℝ) : ℂ) + (H : ℂ) * I) := by
    rw [show (x : ℂ) + (-H : ℂ) * I = -(((-x : ℝ) : ℂ) + (H : ℂ) * I) by push_cast; ring]
    exact zetaDivisorWeightKernel_neg q _
  unfold HIntegral
  calc
    _ = -∫ x in (-1 : ℝ)..1, zetaDivisorWeightKernel (-q) (((-x : ℝ) : ℂ) + (H : ℂ) * I) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr (fun x _ => by simpa only [ofReal_neg] using hpoint x)
    _ = _ := by
      have h := intervalIntegral.integral_comp_neg
        (f := fun x : ℝ => zetaDivisorWeightKernel (-q) ((x : ℂ) + (H : ℂ) * I))
        (a := (-1 : ℝ)) (b := 1)
      simpa only [neg_neg] using congrArg Neg.neg h

theorem vIntegral_zetaDivisorWeight_left (q : ℂ) (H : ℝ) :
    VIntegral (zetaDivisorWeightKernel q) (-1) (-H) H =
      -VIntegral (zetaDivisorWeightKernel (-q)) 1 (-H) H := by
  have hpoint (y : ℝ) :
      zetaDivisorWeightKernel q ((-1 : ℂ) + (y : ℂ) * I) =
        -zetaDivisorWeightKernel (-q) (1 + ((-y : ℝ) : ℂ) * I) := by
    rw [show (-1 : ℂ) + (y : ℂ) * I = -(1 + ((-y : ℝ) : ℂ) * I) by push_cast; ring]
    exact zetaDivisorWeightKernel_neg q _
  have hraw : (∫ y in -H..H, zetaDivisorWeightKernel q ((-1 : ℂ) + (y : ℂ) * I)) =
      -(∫ y in -H..H, zetaDivisorWeightKernel (-q) (1 + (y : ℂ) * I)) := by
    calc
      _ = -∫ y in -H..H, zetaDivisorWeightKernel (-q) (1 + ((-y : ℝ) : ℂ) * I) := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr (fun y _ => hpoint y)
      _ = _ := by
        have h := intervalIntegral.integral_comp_neg
          (f := fun y : ℝ => zetaDivisorWeightKernel (-q) (1 + (y : ℂ) * I)) (a := -H) (b := H)
        simpa only [neg_neg] using congrArg Neg.neg h
  unfold VIntegral
  norm_num only [ofReal_neg, ofReal_one]
  rw [hraw]
  simp

theorem zetaDivisorWeight_truncated_reflection (q : ℂ) {H : ℝ} (hH : 0 < H) :
    VIntegral' (zetaDivisorWeightKernel q) 1 (-H) H +
      VIntegral' (zetaDivisorWeightKernel (-q)) 1 (-H) H -
      HIntegral' (zetaDivisorWeightKernel q) (-1) 1 H -
      HIntegral' (zetaDivisorWeightKernel (-q)) (-1) 1 H = 1 := by
  have hrect := zetaDivisorWeight_finiteRectangle q hH
  rw [show RectangleIntegral' (zetaDivisorWeightKernel q)
        ((-1 : ℂ) - (H : ℂ) * I) ((1 : ℂ) + (H : ℂ) * I) =
      VIntegral' (zetaDivisorWeightKernel q) 1 (-H) H +
        VIntegral' (zetaDivisorWeightKernel (-q)) 1 (-H) H -
        HIntegral' (zetaDivisorWeightKernel q) (-1) 1 H -
        HIntegral' (zetaDivisorWeightKernel (-q)) (-1) 1 H by
    unfold RectangleIntegral' RectangleIntegral HIntegral' VIntegral'
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, neg_re, neg_im,
      one_re, one_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, zero_sub, add_zero, zero_add, neg_zero]
    rw [hIntegral_zetaDivisorWeight_bottom, vIntegral_zetaDivisorWeight_left]
    ring] at hrect
  exact hrect

theorem tendsto_zetaDivisorWeight_vertical (q : ℂ) :
    Tendsto (fun H : ℝ => VIntegral' (zetaDivisorWeightKernel q) 1 (-H) H)
      atTop (𝓝 (zetaDivisorWeight q)) := by
  have h := (intervalIntegral_tendsto_integral (integrable_zetaDivisorWeightKernel_right q)
    tendsto_neg_atTop_atBot tendsto_id).const_mul (1 / (2 * Real.pi) : ℂ)
  convert h using 1
  · funext H
    unfold VIntegral' VIntegral
    simp only [smul_eq_mul, Complex.ofReal_one]
    field_simp [Real.pi_ne_zero]
    rfl

  · rfl

/-- The small-argument estimate comes from the actual residue and both
complete vertical contours, not a declared cutoff convention. -/
theorem zetaDivisorWeight_add_neg (q : ℂ) : zetaDivisorWeight q + zetaDivisorWeight (-q) = 1 := by
  have h := (((tendsto_zetaDivisorWeight_vertical q).add (tendsto_zetaDivisorWeight_vertical (-q))).sub
    (tendsto_zetaDivisorWeight_horizontal_zero q)).sub (tendsto_zetaDivisorWeight_horizontal_zero (-q))
  simp only [sub_zero] at h
  have hconst : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 (zetaDivisorWeight q + zetaDivisorWeight (-q))) := by
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    exact zetaDivisorWeight_truncated_reflection q hH
  exact tendsto_nhds_unique hconst tendsto_const_nhds

theorem zetaDivisorWeight_zero : zetaDivisorWeight 0 = 1 / 2 := by
  have h := zetaDivisorWeight_add_neg 0
  simp only [neg_zero] at h
  linear_combination h / 2

/-- Bounded on the small side and exponentially decaying on the large
side, uniformly across the entire specified horizontal strip. -/
theorem exists_norm_zetaDivisorWeight_min_le {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℂ, |q.im| ≤ B →
      ‖zetaDivisorWeight q‖ ≤ C * min 1 (Real.exp (-q.re)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaDivisorWeight_le hB
  refine ⟨1 + C, by positivity, ?_⟩
  intro q hq
  by_cases hqr : 0 ≤ q.re
  · rw [min_eq_right (Real.exp_le_one_iff.mpr (by linarith))]
    apply (hbound q hq).trans
    nlinarith [Real.exp_pos (-q.re)]
  · have hqr' : q.re ≤ 0 := le_of_not_ge hqr
    rw [min_eq_left (Real.one_le_exp (by linarith)), mul_one]
    have heq : zetaDivisorWeight q = 1 - zetaDivisorWeight (-q) := by
      linear_combination zetaDivisorWeight_add_neg q
    rw [heq]
    have hm := hbound (-q) (by simpa using hq)
    simp only [neg_re, neg_neg] at hm
    have he := Real.exp_le_one_iff.mpr hqr'
    have hn := norm_sub_le (1 : ℂ) (zetaDivisorWeight (-q))
    simp only [norm_one] at hn
    nlinarith

end MathCollab.Density.Stronger.Atkinson
