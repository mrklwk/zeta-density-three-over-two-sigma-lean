module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_CUTOFF_C2_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Second-order composition in the actual real source variable

The chain rule is proved from local smoothness and derivative
identities. It retains both terms of the second derivative.
-/

noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem iteratedDeriv_ofReal_fun {f : ℝ → ℝ} {j : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ j f x) :
    iteratedDeriv j (fun y => (f y : ℂ)) x = ((iteratedDeriv j f x : ℝ) : ℂ) := by
  simpa only [Complex.real_smul, mul_one] using! iteratedDeriv_smul_const hf (1 : ℂ)

theorem iteratedDeriv_two_comp_real {f : ℝ → ℂ} {g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun y => f (g y)) x =
      (deriv g x) ^ 2 • iteratedDeriv 2 f (g x) +
        iteratedDeriv 2 g x • deriv f (g x) := by
  have he : deriv (fun y => f (g y)) =ᶠ[𝓝 x]
      fun y => deriv g y • deriv f (g y) := by
    filter_upwards [hg.eventually (by norm_num),
      hg.continuousAt.eventually (hf.eventually (by norm_num))] with y hgy hfy
    exact (hfy.differentiableAt (by norm_num)).hasDerivAt.scomp
      y (hgy.differentiableAt (by norm_num)).hasDerivAt |>.deriv
  have hdg := ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hdf := ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have h := hdg.smul (hdf.scomp x (hg.differentiableAt (by norm_num)).hasDerivAt)
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  convert h.deriv using 1
  · rfl
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, real_smul, Complex.ofReal_pow,
      Function.comp_apply]
    ring

theorem IntervalC2Bound.congr_of_eventuallyEq {f g : ℝ → ℂ} {a b M R : ℝ}
    (hf : IntervalC2Bound f a b M R)
    (he : ∀ x ∈ Icc a b, f =ᶠ[𝓝 x] g) :
    IntervalC2Bound g a b M R := by
  refine ⟨hf.nonneg, hf.scale_nonneg, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hf.smooth x hx).congr_of_eventuallyEq (he x hx).symm
  · intro x hx
    rw [← (he x hx).eq_of_nhds]
    exact hf.norm_le x hx
  · intro x hx
    rw [← (he x hx).deriv_eq]
    exact hf.deriv_le x hx
  · intro x hx
    rw [← (he x hx).iteratedDeriv_eq 2]
    exact hf.second_le x hx

theorem IntervalC2Bound.absorb_scale {f : ℝ → ℂ} {a b M K R : ℝ}
    (hf : IntervalC2Bound f a b M (K * R)) (hK : 1 ≤ K) (hR : 0 ≤ R) :
    IntervalC2Bound f a b (M * K ^ 2) R := by
  have hK0 : 0 ≤ K := by linarith
  have hKsq : K ≤ K ^ 2 := by nlinarith
  refine ⟨mul_nonneg hf.nonneg (sq_nonneg _), hR, hf.smooth, ?_, ?_, ?_⟩
  · intro x hx
    apply (hf.norm_le x hx).trans
    nlinarith [mul_nonneg hf.nonneg (show 0 ≤ K ^ 2 - 1 by nlinarith)]
  · intro x hx
    apply (hf.deriv_le x hx).trans
    have h := mul_le_mul_of_nonneg_left hKsq (mul_nonneg hf.nonneg hR)
    nlinarith
  · intro x hx
    convert hf.second_le x hx using 1
    ring

theorem exists_real_profile_derivative_bound {v : ℝ → ℝ} {a b : ℝ}
    (hv : ∀ u ∈ Icc a b, ContDiffAt ℝ 2 v u) :
    ∃ M : ℝ, 0 < M ∧ ∀ u ∈ Icc a b,
      |v u| ≤ M ∧ |deriv v u| ≤ M ∧ |iteratedDeriv 2 v u| ≤ M := by
  obtain ⟨M, hM, hm⟩ := exists_intervalC2Bound_fixed (f := fun u => (v u : ℂ))
    (fun u hu => Complex.ofRealCLM.contDiff.contDiffAt.comp u (hv u hu))
  have hv0 (u : ℝ) (hu : u ∈ Icc a b) : |v u| ≤ M := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hm.norm_le u hu
  have hv1 (u : ℝ) (hu : u ∈ Icc a b) : |deriv v u| ≤ M := by
    have he := iteratedDeriv_ofReal_fun ((hv u hu).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
    simp only [iteratedDeriv_one] at he
    have hb := hm.deriv_le u hu
    rw [he, Complex.norm_real, Real.norm_eq_abs, mul_one] at hb
    exact hb
  have hv2 (u : ℝ) (hu : u ∈ Icc a b) : |iteratedDeriv 2 v u| ≤ M := by
    have he := iteratedDeriv_ofReal_fun (hv u hu)
    have hb := hm.second_le u hu
    rw [he, Complex.norm_real, Real.norm_eq_abs, one_pow, mul_one] at hb
    exact hb
  exact ⟨M, hM, fun u hu => ⟨hv0 u hu, hv1 u hu, hv2 u hu⟩⟩

end MathCollab.Density.Stronger.Atkinson
