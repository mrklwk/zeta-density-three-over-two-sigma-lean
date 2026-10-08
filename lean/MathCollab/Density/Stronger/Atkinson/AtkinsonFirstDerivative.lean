module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import WeylPort.Analytic.NonstationaryFoundation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# First-derivative estimates in both orientations

These are proved applications of the native monotone reciprocal-slope
test. Positive slopes are reflected with the exact interval change
of variables. The actual root-phase consumers derive all hypotheses.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem norm_phaseIntegral_le_of_negative_slope {φ : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hslope : ∀ x ∈ Icc a b, deriv φ x ≤ -lam)
    (hmono : AntitoneOn (deriv φ) (Icc a b)) :
    ‖∫ x in a..b, Complex.exp (2 * Real.pi * I * (φ x : ℂ))‖ ≤ 1 / (lam * Real.pi) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  have hne (x : ℝ) (hx : x ∈ Icc a b) : deriv φ x ≠ 0 := by
    have h := hslope x hx
    linarith
  have hcont : ContinuousOn (fun x => 1 / deriv φ x) (Icc a b) := by
    intro x hx
    exact (continuousAt_const.div
      (((hφ x hx).derivWithin (m := 1) (by norm_num)).continuousAt)
      (hne x hx)).continuousWithinAt
  have hanti : AntitoneOn (fun x => |1 / deriv φ x|) (Icc a b) := by
    intro x hx y hy hxy
    have hxneg : deriv φ x < 0 := lt_of_le_of_lt (hslope x hx) (by linarith)
    have hyneg : deriv φ y < 0 := lt_of_le_of_lt (hslope y hy) (by linarith)
    change |1 / deriv φ y| ≤ |1 / deriv φ x|
    rw [abs_div, abs_div, abs_one, abs_of_neg hxneg, abs_of_neg hyneg]
    exact one_div_le_one_div_of_le (by linarith) (neg_le_neg (hmono hx hy hxy))
  have h := ZetaAppendix.nonstationary_phase_integral_bound hab' φ
    (fun x hx => ((hφ x hx).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffWithinAt)
    hne (fun _ => 1) (fun x => 1 / deriv φ x) (fun _ => rfl) hcont hanti
  have hi : ‖∫ x in a..b, Complex.exp (2 * Real.pi * I * (φ x : ℂ))‖ ≤
      |1 / deriv φ a| / Real.pi := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    simpa only [Complex.ofReal_one, one_mul] using h
  apply hi.trans
  have ha : deriv φ a ≤ -lam := hslope a ⟨le_rfl, hab⟩
  rw [abs_div, abs_one, abs_of_neg (by linarith : deriv φ a < 0)]
  have hrec := one_div_le_one_div_of_le hlam (show lam ≤ -deriv φ a by linarith)
  have hfin := div_le_div_of_nonneg_right hrec Real.pi_pos.le
  convert hfin using 1
  ring

theorem norm_phaseIntegral_le_of_positive_slope {φ : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hslope : ∀ x ∈ Icc a b, lam ≤ deriv φ x)
    (hmono : AntitoneOn (deriv φ) (Icc a b)) :
    ‖∫ x in a..b, Complex.exp (2 * Real.pi * I * (φ x : ℂ))‖ ≤ 1 / (lam * Real.pi) := by
  have hmem (x : ℝ) (hx : x ∈ Icc (-b) (-a)) : -x ∈ Icc a b := by
    constructor <;> linarith [hx.1, hx.2]
  have hd (x : ℝ) (hx : x ∈ Icc (-b) (-a)) :
      deriv (fun y => φ (-y)) x = -deriv φ (-x) := by
    have h := (((hφ (-x) (hmem x hx)).differentiableAt (by norm_num)).hasDerivAt.comp
      x (hasDerivAt_neg x)).deriv
    simpa only [mul_neg_one, Function.comp_def] using! h
  have h := norm_phaseIntegral_le_of_negative_slope
    (φ := fun y => φ (-y)) (by linarith : -b ≤ -a) hlam
    (fun x hx => (hφ (-x) (hmem x hx)).comp x (by fun_prop))
    (fun x hx => by rw [hd x hx]; exact neg_le_neg (hslope (-x) (hmem x hx)))
    (by
      intro x hx y hy hxy
      rw [hd x hx, hd y hy]
      exact neg_le_neg (hmono (hmem y hy) (hmem x hx) (by linarith)))
  rw [intervalIntegral.integral_comp_neg
    (f := fun x => Complex.exp (2 * Real.pi * I * (φ x : ℂ)))] at h
  simpa only [neg_neg] using h


end MathCollab.Density.Stronger.Atkinson
