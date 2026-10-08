module
-- Reversible module-visibility port of the audited development.
/-
Native point-mean Gamma-kernel slice, inspired by Scott McColm's
PointMeanGammaKernel.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_RECTANGLE_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The proof here uses local beta-strip comparison, not the source's digamma shift.
The imported GammaStrip retains its upstream Apache-2.0 attribution.
-/
public import MathCollab.Density.GammaStrip
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex
open MathCollab.Density.GammaBounds
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- Retain the full pi/2 exponential rate in the exact half-line formula. -/
theorem norm_Gamma_half_vertical_le_exp (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      3 * Real.exp (-(Real.pi * |t|) / 2) := by
  have hsq : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
    have h := norm_Gamma_centralPoint_sq t
    change ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 = _ at h
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using h
  have hcosh := exp_abs_le_two_mul_cosh (Real.pi * t)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hcosh
  have hsq_le : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
    rw [hsq, Real.exp_neg]
    change Real.pi / Real.cosh (Real.pi * t) ≤
      (2 * Real.pi) / Real.exp (Real.pi * |t|)
    apply (div_le_div_iff₀ (Real.cosh_pos _) (Real.exp_pos _)).2
    nlinarith [Real.pi_pos]
  have hsq_final : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (3 * Real.exp (-(Real.pi * |t|) / 2)) ^ 2 := by
    calc
      _ ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := hsq_le
      _ ≤ 9 * Real.exp (-(Real.pi * |t|)) := by
        gcongr
        linarith [Real.pi_le_four]
      _ = _ := by
        rw [show -(Real.pi * |t|) =
          -(Real.pi * |t|) / 2 + -(Real.pi * |t|) / 2 by ring, Real.exp_add]
        ring
  nlinarith [norm_nonneg (Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)),
    Real.exp_pos (-(Real.pi * |t|) / 2)]

/-- The harmless linear factor costs only part of the exponential reserve. -/
theorem add_one_mul_exp_neg_pi_half_le (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(Real.pi * x) / 2) ≤
      6 * Real.exp (-(4 / 3 : ℝ) * x) := by
  have hLower : 1 + x / 6 ≤ Real.exp (x / 6) := by
    simpa [add_comm] using Real.add_one_le_exp (x / 6)
  have hRate : x / 6 ≤ (Real.pi / 2 - 4 / 3) * x := by
    nlinarith [Real.pi_gt_three]
  have hLinear : 1 + x ≤ 6 * Real.exp ((Real.pi / 2 - 4 / 3) * x) := by
    calc
      1 + x ≤ 6 * (1 + x / 6) := by linarith
      _ ≤ 6 * Real.exp (x / 6) := by gcongr
      _ ≤ 6 * Real.exp ((Real.pi / 2 - 4 / 3) * x) := by gcongr
  calc
    _ ≤ (6 * Real.exp ((Real.pi / 2 - 4 / 3) * x)) *
        Real.exp (-(Real.pi * x) / 2) := by gcongr
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf

/-- Uniform strong exponential Gamma bound, with an explicit absolute constant. -/
theorem norm_Gamma_positive_strip_strong {a v : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) :
    ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
      72 * Real.exp (-(4 / 3 : ℝ) * |v|) := by
  let z : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [z] at hr
  have hrec : Complex.Gamma (stripPoint (3 / 2) v) = z * Complex.Gamma z := by
    convert Complex.Gamma_add_one z hz using 1
    congr 1
    dsimp [stripPoint, z]
    push_cast
    ring
  have hnorm : ‖z‖ ≤ 1 + |v| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    norm_num [z] at h
    linarith
  calc
    _ ≤ 4 * ‖Complex.Gamma (stripPoint (3 / 2) v)‖ :=
      norm_Gamma_stripPoint_le_four_upper ha ha'
    _ = 4 * (‖z‖ * ‖Complex.Gamma z‖) := by rw [hrec, norm_mul]
    _ ≤ 4 * ((1 + |v|) * (3 * Real.exp (-(Real.pi * |v|) / 2))) := by
      gcongr
      exact norm_Gamma_half_vertical_le_exp v
    _ = 12 * ((1 + |v|) * Real.exp (-(Real.pi * |v|) / 2)) := by ring
    _ ≤ 12 * (6 * Real.exp (-(4 / 3 : ℝ) * |v|)) := by
      exact mul_le_mul_of_nonneg_left
        (add_one_mul_exp_neg_pi_half_le |v| (abs_nonneg v)) (by norm_num)
    _ = _ := by ring

/-- Both displaced Gamma kernels, including ordinate zero; the singular
factor is retained and the constant precedes delta and v. -/
theorem Gamma_displaced_strong_bound {a v : ℝ}
    (ha : -(1 / 2 : ℝ) ≤ a) (ha' : a ≤ 1 / 2) (ha0 : a ≠ 0) :
    (|a| + |v|) * ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
      144 * Real.exp (-(4 / 3 : ℝ) * |v|) := by
  let z : ℂ := (a : ℂ) + (v : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    apply ha0
    simpa [z] using congrArg Complex.re h
  have hcoord : |a| + |v| ≤ 2 * ‖z‖ := by
    have hr := Complex.abs_re_le_norm z
    have hi := Complex.abs_im_le_norm z
    simp only [z, add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, sub_self, add_zero, add_im, mul_im, mul_one, zero_add] at hr hi
    linarith
  have hshift : z + 1 = ((a + 1 : ℝ) : ℂ) + (v : ℂ) * I := by
    dsimp [z]
    push_cast
    ring
  have hg := norm_Gamma_positive_strip_strong
    (a := a + 1) (v := v) (by linarith) (by linarith)
  rw [← hshift, Complex.Gamma_add_one z hz, norm_mul] at hg
  change (|a| + |v|) * ‖Complex.Gamma z‖ ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hcoord (norm_nonneg (Complex.Gamma z))]

theorem heathBrown_Gamma_shift_kernel_strong_bound {δ v : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (δ + |v|) * ‖Complex.Gamma ((δ : ℂ) + (v : ℂ) * I)‖ ≤
        144 * Real.exp (-(4 / 3 : ℝ) * |v|) ∧
    (δ + |v|) * ‖Complex.Gamma (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        144 * Real.exp (-(4 / 3 : ℝ) * |v|) := by
  constructor
  · simpa only [abs_of_pos hδ] using Gamma_displaced_strong_bound
      (a := δ) (v := v) (by linarith) hδ' hδ.ne'
  · simpa only [abs_neg, abs_of_pos hδ] using Gamma_displaced_strong_bound
      (a := -δ) (v := v) (by linarith) (by linarith) (neg_ne_zero.mpr hδ.ne')

end MathCollab.Density.Stronger.PointMean
