module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Provenance: ../../../../../third_party/twelfth/ATKINSON_GAUSSIAN_MANIFEST.json.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.GammaPhase
public import MathCollab.Density.Stronger.Atkinson.QuadraticGaussian
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


/-- The local logarithm expansion, with an explicit closed-window error. -/
theorem abs_log_shift_sub_linear_le {T x : ℝ} (hT : 0 < T) (hx : |x| ≤ T / 2) :
    |Real.log (T + x) - Real.log T - x / T| ≤ 2 * x ^ 2 / T ^ 2 := by
  have hu : |-(x / T)| ≤ 1 / 2 := by
    rw [abs_neg, abs_div, abs_of_pos hT]
    exact (div_le_iff₀ hT).mpr (by linarith)
  have h := Real.abs_log_sub_add_sum_range_le (lt_of_le_of_lt hu (by norm_num)) 1
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_one,
    pow_one, div_one] at h
  have habs : |-(x / T)| = |x| / T := by rw [abs_neg, abs_div, abs_of_pos hT]
  rw [habs] at h
  have hpos : 0 < 1 - -(x / T) := by
    have := (abs_le.mp hu).2
    linarith
  have hfactor : T + x = T * (1 - -(x / T)) := by field_simp; ring
  have hlog : Real.log (T + x) = Real.log T + Real.log (1 - -(x / T)) := by
    rw [hfactor, Real.log_mul hT.ne' hpos.ne']
  have hden : 0 < 1 - |x| / T := by rw [habs] at hu; linarith
  have hmain : |Real.log (T + x) - Real.log T - x / T| =
      |-(x / T) + Real.log (1 - -(x / T))| := by rw [hlog]; congr 1; ring
  rw [hmain]
  refine h.trans ?_
  apply (div_le_iff₀ hden).mpr
  have hsmall : |x| / T ≤ 1 / 2 := by rw [← habs]; exact hu
  rw [div_pow, sq_abs]
  calc
    x ^ 2 / T ^ 2 = (x ^ 2 / T ^ 2) * 1 := by ring
    _ ≤ (x ^ 2 / T ^ 2) * (2 * (1 - |x| / T)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

def zetaSquareGammaQuadraticAngle (T x : ℝ) : ℝ :=
  x * Real.log (T / (2 * Real.pi)) + x ^ 2 / (2 * T)

theorem hasDerivAt_zetaSquareGammaQuadraticAngle {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (zetaSquareGammaQuadraticAngle T)
      (Real.log (T / (2 * Real.pi)) + x / T) x := by
  convert ((hasDerivAt_id x).mul_const (Real.log (T / (2 * Real.pi)))).add
    ((hasDerivAt_pow 2 x).div_const (2 * T)) using 1
  · rfl
  · norm_num
    field_simp

theorem abs_zetaSquareGammaFrequency_linear_error_le {T r x : ℝ}
    (hT : 4 ≤ T) (hr : r ≤ T / 2) (hx : |x| ≤ r) :
    |zetaSquareGammaFrequency (T + x) + Real.log (T / (2 * Real.pi)) + x / T| ≤
      18 / T + 2 * r ^ 2 / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hxT : |x| ≤ T / 2 := hx.trans hr
  have ht : 2 ≤ T + x := by have := (abs_le.mp hxT).1; linarith
  have ht0 : 0 < T + x := by linarith
  have hfreq := abs_zetaSquareGammaFrequency_add_log_le ht
  have hlog := abs_log_shift_sub_linear_le hT0 hxT
  have hlogdiff : Real.log ((T + x) / (2 * Real.pi)) - Real.log (T / (2 * Real.pi)) =
      Real.log (T + x) - Real.log T := by
    rw [Real.log_div ht0.ne' (mul_ne_zero two_ne_zero Real.pi_ne_zero),
      Real.log_div hT0.ne' (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
    ring
  have heq : zetaSquareGammaFrequency (T + x) + Real.log (T / (2 * Real.pi)) + x / T =
      (zetaSquareGammaFrequency (T + x) + Real.log ((T + x) / (2 * Real.pi))) -
      (Real.log (T + x) - Real.log T - x / T) := by rw [← hlogdiff]; ring
  rw [heq]
  refine (abs_sub _ _).trans ((add_le_add hfreq hlog).trans (add_le_add ?_ ?_))
  · apply (div_le_div_iff₀ ht0 hT0).mpr
    have := (abs_le.mp hxT).1
    linarith
  · apply div_le_div_of_nonneg_right _ (sq_nonneg T)
    have := sq_le_sq₀ (abs_nonneg x) ((abs_nonneg x).trans hx)
    have hs : x ^ 2 ≤ r ^ 2 := by simpa only [sq_abs] using this.mpr hx
    linarith

private def demodulatedGammaPhase (T x : ℝ) : ℂ :=
  zetaSquareReflectedGammaPhase (T + x) *
    Complex.exp (I * (zetaSquareGammaQuadraticAngle T x : ℂ))

private theorem hasDerivAt_demodulatedGammaPhase {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (demodulatedGammaPhase T)
      (I * ((zetaSquareGammaFrequency (T + x) + Real.log (T / (2 * Real.pi)) + x / T : ℝ) : ℂ) *
        demodulatedGammaPhase T x) x := by
  have hphase := (hasDerivAt_zetaSquareReflectedGammaPhase (T + x)).scomp x
    ((hasDerivAt_id x).const_add T)
  have hexp := (((hasDerivAt_zetaSquareGammaQuadraticAngle hT x).ofReal_comp).const_mul I).cexp
  convert hphase.mul hexp using 1
  · rfl
  · simp only [Function.comp_apply, one_smul, demodulatedGammaPhase, Complex.ofReal_add]
    ring

/-- The actual Gamma quotient, with the negative quadratic phase used by
the Gaussian transform. Both window endpoints and the centre are included. -/
theorem norm_zetaSquareReflectedGammaPhase_sub_quadratic_le {T r x : ℝ}
    (hT : 4 ≤ T) (hr : r ≤ T / 2) (hx : |x| ≤ r) :
    ‖zetaSquareReflectedGammaPhase (T + x) -
      zetaSquareReflectedGammaPhase T *
        Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ))‖ ≤
      (18 / T + 2 * r ^ 2 / T ^ 2) * |x| := by
  have hT0 : 0 < T := by linarith
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hx
  have hnorm (u : ℝ) : ‖demodulatedGammaPhase T u‖ = 1 := by
    simp [demodulatedGammaPhase, norm_zetaSquareReflectedGammaPhase,
      Complex.norm_exp]
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := demodulatedGammaPhase T)
    (f' := fun u => I * ((zetaSquareGammaFrequency (T + u) +
      Real.log (T / (2 * Real.pi)) + u / T : ℝ) : ℂ) * demodulatedGammaPhase T u)
    (s := Icc (-r) r) (x := 0) (y := x)
    (fun u _ => (hasDerivAt_demodulatedGammaPhase hT0.ne' u).hasDerivWithinAt)
    (C := 18 / T + 2 * r ^ 2 / T ^ 2) ?_ (convex_Icc _ _)
    (by constructor <;> linarith) (abs_le.mp hx)
  · have heq : zetaSquareReflectedGammaPhase (T + x) -
        zetaSquareReflectedGammaPhase T * Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ)) =
        (demodulatedGammaPhase T x - demodulatedGammaPhase T 0) *
          Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ)) := by
      simp only [demodulatedGammaPhase, zetaSquareGammaQuadraticAngle, zero_mul, add_zero]
      rw [sub_mul, mul_assoc, ← Complex.exp_add]
      ring_nf
      simp
    rw [heq, norm_mul]
    have he : ‖Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ))‖ = 1 := by
      simp [Complex.norm_exp]
    rw [he, mul_one]
    simpa only [sub_zero, Real.norm_eq_abs] using hbound
  intro u hu
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, hnorm,
    one_mul, mul_one]
  exact abs_zetaSquareGammaFrequency_linear_error_le hT hr (abs_le.mpr hu)

/-- Exact identification of the approximating oscillation with the physical
quadratic Gaussian kernel, including its shifted frequency. -/
theorem zetaSquareGammaQuadratic_gaussian_identity (T G v x : ℝ) :
    Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ)) *
      Complex.exp (I * (v : ℂ) * x) * ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ) =
      Complex.exp (I * ((v - Real.log (T / (2 * Real.pi)) : ℝ) : ℂ) * x) *
        Complex.exp (-zetaGaussianQuadraticCoefficient T G * (x : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold zetaSquareGammaQuadraticAngle zetaGaussianQuadraticCoefficient
  push_cast
  field_simp
  ring

/-- Integrated phase replacement on the actual closed physical window.
The bound is uniform in the real frequency. It does not remove the
remaining shifted-Gamma amplitude from the divisor source. -/
theorem norm_integral_zetaSquareGammaPhase_sub_quadratic_le {T r G : ℝ}
    (hT : 4 ≤ T) (hr0 : 0 ≤ r) (hr : r ≤ T / 2) (v : ℝ) :
    ‖(∫ x in -r..r, zetaSquareReflectedGammaPhase (T + x) *
        Complex.exp (I * (v : ℂ) * x) * ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)) -
      zetaSquareReflectedGammaPhase T *
        ∫ x in -r..r, Complex.exp (I * ((v - Real.log (T / (2 * Real.pi)) : ℝ) : ℂ) * x) *
          Complex.exp (-zetaGaussianQuadraticCoefficient T G * (x : ℂ) ^ 2)‖ ≤
      2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) := by
  let C : ℝ := 18 / T + 2 * r ^ 2 / T ^ 2
  have hT0 : 0 < T := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hphase : Continuous zetaSquareReflectedGammaPhase :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_zetaSquareReflectedGammaPhase t).continuousAt)
  have hleft : Continuous (fun x : ℝ => zetaSquareReflectedGammaPhase (T + x) *
      Complex.exp (I * (v : ℂ) * x) * ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)) := by
    fun_prop (disch := assumption)
  have hright : Continuous (fun x : ℝ => Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ)) *
      Complex.exp (I * (v : ℂ) * x) * ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)) := by
    unfold zetaSquareGammaQuadraticAngle
    fun_prop
  have heq : (∫ x in -r..r, zetaSquareReflectedGammaPhase (T + x) *
        Complex.exp (I * (v : ℂ) * x) * ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)) -
      zetaSquareReflectedGammaPhase T *
        ∫ x in -r..r, Complex.exp (I * ((v - Real.log (T / (2 * Real.pi)) : ℝ) : ℂ) * x) *
          Complex.exp (-zetaGaussianQuadraticCoefficient T G * (x : ℂ) ^ 2) =
      ∫ x in -r..r, (zetaSquareReflectedGammaPhase (T + x) -
        zetaSquareReflectedGammaPhase T * Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ))) *
          Complex.exp (I * (v : ℂ) * x) * ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ) := by
    simp_rw [← zetaSquareGammaQuadratic_gaussian_identity T G v]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hleft.intervalIntegrable _ _)
        ((hright.const_mul _).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [heq]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -r) (b := r) (C := C * r)
    (f := fun x : ℝ => (zetaSquareReflectedGammaPhase (T + x) -
        zetaSquareReflectedGammaPhase T * Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ))) *
          Complex.exp (I * (v : ℂ) * x) * ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)) ?_
  · rw [abs_of_nonneg (by linarith : 0 ≤ r - -r)] at hbound
    convert hbound using 1
    dsimp [C]
    ring
  intro x hx
  rw [uIoc_of_le (by linarith : -r ≤ r)] at hx
  have hxr : |x| ≤ r := abs_le.mpr ⟨hx.1.le, hx.2⟩
  have hp := norm_zetaSquareReflectedGammaPhase_sub_quadratic_le hT hr hxr
  have he : ‖Complex.exp (I * (v : ℂ) * (x : ℂ))‖ = 1 := by simp [Complex.norm_exp]
  have hw : ‖((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  change ‖(_ : ℂ) * _ * _‖ ≤ C * r
  rw [norm_mul, norm_mul, he, mul_one]
  calc
    _ ≤ ‖zetaSquareReflectedGammaPhase (T + x) - zetaSquareReflectedGammaPhase T *
        Complex.exp (-I * (zetaSquareGammaQuadraticAngle T x : ℂ))‖ * 1 :=
      mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ ≤ C * r := by rw [mul_one]; exact hp.trans (mul_le_mul_of_nonneg_left hxr hC)

end MathCollab.Density.Stronger.Atkinson
