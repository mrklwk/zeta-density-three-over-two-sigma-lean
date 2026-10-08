module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonBandCancellation

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Quantitative reciprocal-slope calculus

The reciprocal bounds retain the actual first and second derivatives.
They will be applied to the nonzero phase slope on the exact source band.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem iteratedDeriv_two_real_inv {g : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hne : g x ≠ 0) :
    iteratedDeriv 2 (fun y => (g y)⁻¹) x =
      2 * (deriv g x) ^ 2 / (g x) ^ 3 - iteratedDeriv 2 g x / (g x) ^ 2 := by
  have he : deriv (fun y => (g y)⁻¹) =ᶠ[𝓝 x] fun y => -deriv g y / (g y) ^ 2 := by
    filter_upwards [hg.eventually (by norm_num), hg.continuousAt.eventually_ne hne] with y hgy hy
    exact deriv_fun_inv'' (hgy.differentiableAt (by norm_num)) hy
  have hd := (hg.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have h := (hdd.neg.div (hd.pow 2) (pow_ne_zero 2 hne)).deriv
  change deriv (fun y => -deriv g y / (g y) ^ 2) x = _ at h
  dsimp only [Pi.neg_apply, Pi.pow_apply] at h
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq, h]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem intervalC2Bound_real_reciprocal {g : ℝ → ℝ} {a c B R : ℝ}
    (hB : 0 < B) (hR : 0 ≤ R) (hg : ∀ x ∈ Icc a c, ContDiffAt ℝ 2 g x)
    (hlo : ∀ x ∈ Icc a c, B ≤ |g x|)
    (hfirst : ∀ x ∈ Icc a c, |deriv g x| ≤ B * R)
    (hsecond : ∀ x ∈ Icc a c, |iteratedDeriv 2 g x| ≤ B * R ^ 2) :
    IntervalC2Bound (fun x => (((g x)⁻¹ : ℝ) : ℂ)) a c (3 / B) R := by
  have hne (x : ℝ) (hx : x ∈ Icc a c) : g x ≠ 0 :=
    abs_pos.mp (hB.trans_le (hlo x hx))
  have hs (x : ℝ) (hx : x ∈ Icc a c) : ContDiffAt ℝ 2 (fun y => (g y)⁻¹) x :=
    (hg x hx).inv (hne x hx)
  refine ⟨by positivity, hR,
    fun x hx => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hs x hx), ?_, ?_, ?_⟩
  · intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv]
    have h := one_div_le_one_div_of_le hB (hlo x hx)
    rw [one_div, one_div] at h
    exact h.trans (by rw [← one_div]; gcongr; norm_num)
  · intro x hx
    have hd := ((hs x hx).differentiableAt (by norm_num)).hasDerivAt.ofReal_comp.deriv
    rw [hd, Complex.norm_real, Real.norm_eq_abs,
      deriv_fun_inv'' ((hg x hx).differentiableAt (by norm_num)) (hne x hx),
      abs_div, abs_neg, abs_pow]
    calc
      _ ≤ (B * R) / B ^ 2 := by gcongr; exact hfirst x hx; exact hlo x hx
      _ ≤ (3 / B) * R := by
        have he : (B * R) / B ^ 2 = R / B := by field_simp
        rw [he, show (3 / B) * R = 3 * (R / B) by ring]
        have hp : 0 ≤ R / B := by positivity
        nlinarith
  · intro x hx
    rw [iteratedDeriv_ofReal_fun (hs x hx), Complex.norm_real, Real.norm_eq_abs,
      iteratedDeriv_two_real_inv (hg x hx) (hne x hx)]
    apply (abs_sub _ _).trans
    simp only [abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * (B * R) ^ 2 / B ^ 3 + (B * R ^ 2) / B ^ 2 := by
        gcongr
        · exact hfirst x hx
        · exact hlo x hx
        · exact hsecond x hx
        · exact hlo x hx
      _ = _ := by field_simp; ring

theorem IntervalC2Bound.deriv_c1 {f : ℝ → ℂ} {a c M R : ℝ}
    (hf : IntervalC2Bound f a c M R) (hac : a ≤ c) :
    IntervalC1Bound (deriv f) a c (M * (R + (c - a) * R ^ 2)) := by
  have hs (x : ℝ) (hx : x ∈ Icc a c) : ContDiffAt ℝ 1 (deriv f) x :=
    (hf.smooth x hx).derivWithin (by norm_num)
  have hdi : IntervalIntegrable (deriv (deriv f)) volume a c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hac]
    exact fun x hx => ((hs x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hlen : 0 ≤ c - a := sub_nonneg.mpr hac
  have hMR : 0 ≤ M * R := mul_nonneg hf.nonneg hf.scale_nonneg
  have hlast : 0 ≤ M * ((c - a) * R ^ 2) := by positivity [hf.nonneg]
  refine ⟨by positivity [hf.nonneg, hf.scale_nonneg], hs, ?_, ?_⟩
  · intro x hx
    exact (hf.deriv_le x hx).trans (by nlinarith)
  · calc
      _ ≤ ∫ x in a..c, M * R ^ 2 := by
        apply intervalIntegral.integral_mono_on hac hdi.norm intervalIntegrable_const
        intro x hx
        simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hf.second_le x hx
      _ ≤ _ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        nlinarith

end MathCollab.Density.Stronger.Atkinson
