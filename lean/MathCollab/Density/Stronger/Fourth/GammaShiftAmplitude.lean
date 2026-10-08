module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See ../../../../../third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/SQUARE_KERNEL_NEAR_MANIFEST.json.
The imported DigammaSeries retains its separate Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.GammaShiftLog
public import Mathlib.Analysis.ODE.Gronwall

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open MathCollab.Density.Stronger
open MathCollab.Density.Stronger.Fourth.Digamma
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

def zetaGammaShiftAmplitude (t : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  (Complex.Gammaℝ (afeCriticalPoint (-t) + (v : ℂ) * w) /
    Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2 *
      Complex.exp (-(v : ℂ) * w * zetaGammaLeadingLog t)

def zetaGammaShiftError (t : ℝ) (w : ℂ) : ℝ := (17 * ‖w‖ + 2 * ‖w‖ ^ 2) / t

theorem zetaGammaShiftError_nonneg {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    0 ≤ zetaGammaShiftError t w := by unfold zetaGammaShiftError; positivity

theorem zetaGammaShiftAmplitude_zero (t : ℝ) (w : ℂ) : zetaGammaShiftAmplitude t w 0 = 1 := by
  have hne := Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint] :
    0 < (afeCriticalPoint (-t)).re)
  simp [zetaGammaShiftAmplitude, hne]

/-- The derivative is of the literal Gamma quotient, not a model amplitude. -/
theorem hasDerivAt_zetaGammaShiftAmplitude (t : ℝ) {w : ℂ} (hw : 0 ≤ w.re)
    {v : ℝ} (hv : 0 ≤ v) :
    HasDerivAt (zetaGammaShiftAmplitude t w)
      (zetaGammaShiftAmplitude t w v * w *
        (Complex.digamma (zetaGammaHalfShift t w v) -
          (zetaGammaLeadingLog t + Complex.log (Real.pi : ℂ)))) v := by
  have hz : 0 < (afeCriticalPoint (-t) + (v : ℂ) * w).re := by
    have h := zetaGammaHalfShift_re_pos t hw hv
    simp only [zetaGammaHalfShift, Complex.div_ofNat_re] at h
    linarith
  have hinner : HasDerivAt (fun z : ℂ => afeCriticalPoint (-t) + z * w) w (v : ℂ) := by
    simpa using ((hasDerivAt_id (v : ℂ)).mul_const w).const_add (afeCriticalPoint (-t))
  have hgamma := ((hasDerivAt_gammaReal hz).comp (v : ℂ) hinner).comp_ofReal
  have hratio := (hgamma.div_const (Complex.Gammaℝ (afeCriticalPoint (-t)))).pow 2
  have hexp := (((hasDerivAt_id v).ofReal_comp.neg.mul_const w).mul_const
    (zetaGammaLeadingLog t)).cexp
  convert hratio.mul hexp using 1 <;> first
  | rfl
  | (norm_num [zetaGammaShiftAmplitude, zetaGammaHalfShift, Function.comp_def]; ring)

theorem amplitude_derivative_norm_le {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t / 2)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ‖zetaGammaShiftAmplitude t w v * w *
      (Complex.digamma (zetaGammaHalfShift t w v) -
        (zetaGammaLeadingLog t + Complex.log (Real.pi : ℂ)))‖ ≤
      zetaGammaShiftError t w * ‖zetaGammaShiftAmplitude t w v‖ := by
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (‖zetaGammaShiftAmplitude t w v‖ * ‖w‖) * ((17 + 2 * ‖w‖) / t) :=
      mul_le_mul_of_nonneg_left (norm_zetaGammaHalfShift_digamma_sub_le ht hwre hw hv)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by unfold zetaGammaShiftError; ring

theorem norm_zetaGammaShiftAmplitude_le {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t / 2)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ‖zetaGammaShiftAmplitude t w v‖ ≤ Real.exp (zetaGammaShiftError t w * v) := by
  let f := zetaGammaShiftAmplitude t w
  let f' := fun u : ℝ => f u * w * (Complex.digamma (zetaGammaHalfShift t w u) -
    (zetaGammaLeadingLog t + Complex.log (Real.pi : ℂ)))
  have hderiv (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' u) u :=
    hasDerivAt_zetaGammaShiftAmplitude t hwre hu.1
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hi : ‖f 0‖ ≤ 1 := by simp [f, zetaGammaShiftAmplitude_zero]
  have hbound : ∀ u ∈ Ico (0 : ℝ) 1, ‖f' u‖ ≤ zetaGammaShiftError t w * ‖f u‖ + 0 := by
    intro u hu
    exact (amplitude_derivative_norm_le ht hwre hw ⟨hu.1, hu.2.le⟩).trans_eq (add_zero _).symm
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hc
    (fun u hu => (hderiv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt) hi hbound v hv
  simpa only [gronwallBound_ε0, sub_zero, one_mul] using h

/-- Uniform relative error, obtained by integrating the genuine normalized
ratio's derivative after its Gronwall estimate. -/
theorem norm_zetaGammaShiftAmplitude_sub_one_le {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t / 2) :
    ‖zetaGammaShiftAmplitude t w 1 - 1‖ ≤
      zetaGammaShiftError t w * Real.exp (zetaGammaShiftError t w) := by
  have hB : 0 ≤ zetaGammaShiftError t w := zetaGammaShiftError_nonneg (by linarith) w
  have hbound (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖zetaGammaShiftAmplitude t w v * w *
        (Complex.digamma (zetaGammaHalfShift t w v) -
          (zetaGammaLeadingLog t + Complex.log (Real.pi : ℂ)))‖ ≤
        zetaGammaShiftError t w * Real.exp (zetaGammaShiftError t w) := by
    apply (amplitude_derivative_norm_le ht hwre hw hv).trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply (norm_zetaGammaShiftAmplitude_le ht hwre hw hv).trans
    exact Real.exp_le_exp.mpr (mul_le_of_le_one_right hB hv.2)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hasDerivAt_zetaGammaShiftAmplitude t hwre hv.1).hasDerivWithinAt)
    hbound (convex_Icc (0 : ℝ) 1)
    (x := 0) (y := 1) (by constructor <;> norm_num) (by constructor <;> norm_num)
  simpa [zetaGammaShiftAmplitude_zero] using h

/-- Absolute error for the actual squared Gamma ratio. The leading
exponential retains both its height power and its signed contour growth. -/
theorem norm_gammaReal_shift_sq_sub_exp_le {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t / 2) :
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
        Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2 - Complex.exp (w * zetaGammaLeadingLog t)‖ ≤
      zetaGammaShiftError t w * Real.exp (zetaGammaShiftError t w) *
        Real.exp ((w * zetaGammaLeadingLog t).re) := by
  have heq : (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
        Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2 - Complex.exp (w * zetaGammaLeadingLog t) =
      (zetaGammaShiftAmplitude t w 1 - 1) * Complex.exp (w * zetaGammaLeadingLog t) := by
    simp only [zetaGammaShiftAmplitude, Complex.ofReal_one, one_mul, neg_mul, sub_mul, mul_assoc,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [heq, norm_mul, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_right (norm_zetaGammaShiftAmplitude_sub_one_le ht hwre hw)
    (Real.exp_pos _).le

theorem zetaGammaLeadingLog_mul_re (t : ℝ) (w : ℂ) :
    (w * zetaGammaLeadingLog t).re = w.re * Real.log (t / (2 * Real.pi)) + w.im * (Real.pi / 2) := by
  simp [zetaGammaLeadingLog, Complex.mul_re]

theorem norm_gammaReal_shift_sq_le_exp {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t/2) :
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
      Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤
      Real.exp (zetaGammaShiftError t w) *
        Real.exp ((w*zetaGammaLeadingLog t).re) := by
  have h := norm_zetaGammaShiftAmplitude_le ht hwre hw (v := 1)
    (by constructor <;> norm_num)
  have he : (Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2 =
      zetaGammaShiftAmplitude t w 1 * Complex.exp (w*zetaGammaLeadingLog t) := by
    simp only [zetaGammaShiftAmplitude, Complex.ofReal_one, one_mul,
      neg_mul, mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, mul_one]
  rw [he, norm_mul, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using h) (by positivity)


end MathCollab.Density.Stronger.Fourth
