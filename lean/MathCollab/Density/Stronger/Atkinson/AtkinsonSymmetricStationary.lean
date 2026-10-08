module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected proof slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow stationary refinement; see third_party/twelfth/ATKINSON_SYMMETRIC_MANIFEST.json.
Mathlib and previously ported PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.StationaryOddRemainder

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact cancellation of both odd stationary corrections

The symmetric quadratic window kills the amplitude's linear term and
the phase's cubic term. The remaining estimate is on the actual local
integral and consumes the constructed second derivative bounds.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonRootQuadraticKernel_reflect (T b y : ℝ) :
    atkinsonRootQuadraticKernel T b
      (2 * atkinsonSaddleRoot (T / (2 * Real.pi)) b - y) =
        atkinsonRootQuadraticKernel T b y := by
  unfold atkinsonRootQuadraticKernel atkinsonRootQuadratic
  congr 3
  ring

theorem integral_atkinsonRootQuadratic_odd (T b H : ℝ) {k : ℕ} (hk : Odd k) :
    (∫ y in (atkinsonSaddleRoot (T/(2*Real.pi)) b-H)..
      (atkinsonSaddleRoot (T/(2*Real.pi)) b+H),
        (((y-atkinsonSaddleRoot (T/(2*Real.pi)) b)^k : ℝ) : ℂ) *
          atkinsonRootQuadraticKernel T b y) = 0 := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  let F : ℝ → ℂ := fun y => (((y-r)^k : ℝ) : ℂ) * atkinsonRootQuadraticKernel T b y
  have hodd (y : ℝ) : F (2*r-y) = -F y := by
    dsimp [F]
    rw [show 2*r-y-r = -(y-r) by ring, hk.neg_pow,
      Complex.ofReal_neg, atkinsonRootQuadraticKernel_reflect]
    ring
  have h := intervalIntegral.integral_comp_sub_left (a := r-H) (b := r+H) F (2*r)
  have hleft : 2*r-(r+H) = r-H := by ring
  have hright : 2*r-(r-H) = r+H := by ring
  simp_rw [hodd] at h
  rw [intervalIntegral.integral_neg, hleft, hright] at h
  change (∫ y in r-H..r+H, F y) = 0
  linear_combination -h / 2

theorem abs_atkinsonRootCubicCorrection_le {T y H : ℝ} (hT : 0 < T) (b : ℝ)
    (hH : 0 ≤ H) (hy : |y-atkinsonSaddleRoot (T/(2*Real.pi)) b| ≤ H) :
    |atkinsonRootCubicCorrection T b y| ≤
      2*T*H^3/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 := by
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T/(2*Real.pi)) b
  rw [atkinsonRootCubicCorrection, abs_mul, abs_of_pos (by positivity : 0 < 2*T/3),
    abs_pow, abs_div, abs_of_pos hr]
  calc
    _ ≤ (2*T/3)*(H/atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 := by gcongr
    _ ≤ _ := by
      have hp : 0 ≤ 2*T*H^3/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 := by positivity
      nlinarith [show (2*T/3)*(H/atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 =
        (2*T*H^3/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^3)/3 by ring]

theorem IntervalC2Bound.atkinsonLocalSymmetric {f : ℝ → ℂ} {a c M R T H : ℝ}
    (hf : IntervalC2Bound f a c M R) (hT : 0 < T) (b : ℝ) (hH : 0 ≤ H)
    (hleft : a ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b-H)
    (hright : atkinsonSaddleRoot (T/(2*Real.pi)) b+H ≤ c)
    (hwindow : H ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b/2) :
    ‖(∫ y in (atkinsonSaddleRoot (T/(2*Real.pi)) b-H)..
        (atkinsonSaddleRoot (T/(2*Real.pi)) b+H), f y * atkinsonRootKernel T b y) -
      f (atkinsonSaddleRoot (T/(2*Real.pi)) b) *
        ∫ y in (atkinsonSaddleRoot (T/(2*Real.pi)) b-H)..
          (atkinsonSaddleRoot (T/(2*Real.pi)) b+H), atkinsonRootQuadraticKernel T b y‖ ≤
      M*(2*R^2*H^3 + 4*R*T*H^5/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 +
        8*T*H^5/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^4 +
        8*T^2*H^7/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^6) := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have horder : r-H ≤ r+H := by linarith
  have hpos : 0 < r-H := by change H ≤ r/2 at hwindow; linarith
  have hmem {y : ℝ} (hy : y ∈ Icc (r-H) (r+H)) : y ∈ Icc a c :=
    ⟨hleft.trans hy.1, hy.2.trans hright⟩
  have hrmem : r ∈ Icc a c := hmem ⟨by linarith, by linarith⟩
  let P : ℝ → ℂ := fun y =>
    f r * atkinsonRootQuadraticKernel T b y +
    deriv f r * (((y-r : ℝ) : ℂ) * atkinsonRootQuadraticKernel T b y) +
    ((2*T/(3*r^3) : ℝ) : ℂ) * I * f r *
      (((y-r : ℝ) : ℂ)^3 * atkinsonRootQuadraticKernel T b y)
  have hq := continuous_atkinsonRootQuadraticKernel T b
  have hlinear : Continuous (fun y : ℝ =>
      ((y-r : ℝ) : ℂ) * atkinsonRootQuadraticKernel T b y) := by fun_prop
  have hcubic : Continuous (fun y : ℝ =>
      ((y-r : ℝ) : ℂ)^3 * atkinsonRootQuadraticKernel T b y) := by fun_prop
  have hquad := hq.intervalIntegrable (μ := volume) (a := r-H) (b := r+H)
  have hlinearInt := hlinear.intervalIntegrable (μ := volume) (a := r-H) (b := r+H)
  have hcubicInt := hcubic.intervalIntegrable (μ := volume) (a := r-H) (b := r+H)
  have hP : IntervalIntegrable P volume (r-H) (r+H) :=
    ((hquad.const_mul (f r)).add (hlinearInt.const_mul (deriv f r))).add
      (hcubicInt.const_mul (((2*T/(3*r^3) : ℝ) : ℂ)*I*f r))
  have hPint : (∫ y in r-H..r+H, P y) =
      f r * ∫ y in r-H..r+H, atkinsonRootQuadraticKernel T b y := by
    have h1 := integral_atkinsonRootQuadratic_odd T b H (k := 1) (by decide)
    have h3 := integral_atkinsonRootQuadratic_odd T b H (k := 3) (by decide)
    simp only [pow_one] at h1
    simp only [Complex.ofReal_pow] at h3
    change (∫ y in r-H..r+H, ((y-r : ℝ) : ℂ)*atkinsonRootQuadraticKernel T b y) = 0 at h1
    change (∫ y in r-H..r+H, ((y-r : ℝ) : ℂ)^3*atkinsonRootQuadraticKernel T b y) = 0 at h3
    dsimp only [P]
    rw [intervalIntegral.integral_add
      ((hquad.const_mul (f r)).add (hlinearInt.const_mul (deriv f r)))
      (hcubicInt.const_mul _),
      intervalIntegral.integral_add (hquad.const_mul (f r))
      (hlinearInt.const_mul (deriv f r))]
    simp only [intervalIntegral.integral_const_mul, h1, h3, mul_zero, add_zero]
  have hactual : IntervalIntegrable (fun y => f y * atkinsonRootKernel T b y)
      volume (r-H) (r+H) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le horder]
    exact fun y hy => ((hf.smooth y (hmem hy)).continuousAt.mul
      (continuousAt_atkinsonRootKernel T b (hpos.trans_le hy.1))).continuousWithinAt
  have hpoint (y : ℝ) (hy : y ∈ Icc (r-H) (r+H)) :
      ‖f y * atkinsonRootKernel T b y - P y‖ ≤
        M*R^2*H^2 + M*R*H*(2*T*H^3/r^3) +
          M*(4*T*H^4/r^4 + 4*T^2*H^6/r^6) := by
    have hyH : |y-r| ≤ H := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have ha := hf.norm_sub_linear_le hH hleft hright hyH
    have hb : ‖f y-f r‖ ≤ M*R*H :=
      (hf.norm_sub_le hrmem (hmem hy)).trans
        (mul_le_mul_of_nonneg_left hyH (mul_nonneg hf.nonneg hf.scale_nonneg))
    have hd := abs_atkinsonRootCubicCorrection_le hT b hH hyH
    have hk : ‖atkinsonRootKernel T b y - atkinsonRootQuadraticKernel T b y *
        (1+(atkinsonRootCubicCorrection T b y : ℂ)*I)‖ ≤
          4*T*H^4/r^4 + 4*T^2*H^6/r^6 := by
      apply (norm_atkinsonRootKernel_sub_cubic_le hT b (hyH.trans hwindow)).trans
      change 4*T*|y-r|^4/r^4 + 4*T^2*|y-r|^6/r^6 ≤ _
      gcongr
    have he : f y*atkinsonRootKernel T b y-P y =
        (f y-f r-((y-r : ℝ) : ℂ)*deriv f r)*atkinsonRootQuadraticKernel T b y +
        (f y-f r)*(atkinsonRootCubicCorrection T b y : ℂ)*I*
          atkinsonRootQuadraticKernel T b y +
        f y*(atkinsonRootKernel T b y-atkinsonRootQuadraticKernel T b y*
          (1+(atkinsonRootCubicCorrection T b y : ℂ)*I)) := by
      dsimp [P, atkinsonRootCubicCorrection]
      push_cast
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul, norm_atkinsonRootQuadraticKernel, norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add (add_le_add ha (mul_le_mul hb hd (abs_nonneg _)
      (mul_nonneg (mul_nonneg hf.nonneg hf.scale_nonneg) hH)))
      (mul_le_mul (hf.norm_le y (hmem hy)) hk (norm_nonneg _) hf.nonneg)
  change ‖(∫ y in r-H..r+H, f y*atkinsonRootKernel T b y) -
    f r * ∫ y in r-H..r+H, atkinsonRootQuadraticKernel T b y‖ ≤ _
  rw [← hPint, ← intervalIntegral.integral_sub hactual hP]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r-H) (b := r+H) (fun y hy => hpoint y (by
      rw [uIoc_of_le horder] at hy
      exact ⟨hy.1.le,hy.2⟩))
  apply hbound.trans_eq
  rw [abs_of_nonneg (by linarith : 0 ≤ r+H-(r-H))]
  ring

end MathCollab.Density.Stronger.Atkinson
