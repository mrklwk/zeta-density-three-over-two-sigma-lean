module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_CUTOFF_C2_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.Atkinson.DivisorBandCutoff

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter Topology
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem support_iteratedDeriv_smoothTransition {j : ℕ} (hj : 0 < j) :
    Function.support (iteratedDeriv j Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  by_contra h
  have hcases : x < 0 ∨ 1 < x := by simpa only [mem_Icc, not_and_or, not_le] using h
  rcases hcases with hleft | hright
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hleft] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact hx (by rw [heq.iteratedDeriv_eq j, iteratedDeriv_const, ite_eq_right (Nat.ne_of_gt hj)])
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hright] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact hx (by rw [heq.iteratedDeriv_eq j, iteratedDeriv_const, ite_eq_right (Nat.ne_of_gt hj)])

theorem exists_norm_iteratedDeriv_smoothTransition_le (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, ‖iteratedDeriv j Real.smoothTransition x‖ ≤ M := by
  by_cases hj : j = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro x
    simp only [hj, iteratedDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  have hc := Real.smoothTransition.contDiff.continuous_iteratedDeriv' j
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨1 + |B|, by positivity, ?_⟩
  intro x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hB x hx).trans (by linarith [le_abs_self B])
  · have hz : iteratedDeriv j Real.smoothTransition x = 0 := by
      by_contra hn
      exact hx (support_iteratedDeriv_smoothTransition (Nat.pos_of_ne_zero hj) hn)
    rw [hz, norm_zero]
    positivity

theorem deriv_smoothTransition_quadratic (c d x : ℝ) :
    deriv (fun y => Real.smoothTransition (c * y ^ 2 + d)) x =
      (2 * c * x) * deriv Real.smoothTransition (c * x ^ 2 + d) := by
  have hq := (((hasDerivAt_id x).pow 2).const_mul c).add_const d
  have h := (((Real.smoothTransition.contDiff : ContDiff ℝ 2 Real.smoothTransition).differentiable
    (by norm_num)).differentiableAt.hasDerivAt.comp
    x hq).deriv
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq]
    ring

theorem iteratedDeriv_two_smoothTransition_quadratic (c d x : ℝ) :
    iteratedDeriv 2 (fun y => Real.smoothTransition (c * y ^ 2 + d)) x =
      (2 * c * x) ^ 2 * iteratedDeriv 2 Real.smoothTransition (c * x ^ 2 + d) +
        (2 * c) * deriv Real.smoothTransition (c * x ^ 2 + d) := by
  have he : deriv (fun y => Real.smoothTransition (c * y ^ 2 + d)) =
      fun y => (2 * c * y) * deriv Real.smoothTransition (c * y ^ 2 + d) :=
    funext (deriv_smoothTransition_quadratic c d)
  have hq := (((hasDerivAt_id x).pow 2).const_mul c).add_const d
  have hd := ((Real.smoothTransition.contDiff : ContDiff ℝ 2 Real.smoothTransition).differentiable_deriv_two
    (c * x ^ 2 + d)).hasDerivAt
  have h := (((hasDerivAt_id x).const_mul (2 * c)).mul (hd.comp x hq)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, he]
  convert h using 1
  · rfl
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_apply, Pi.pow_apply, id_eq]
    ring

theorem exists_intervalC2Bound_quadraticTransition :
    ∃ M : ℝ, 0 < M ∧ ∀ c d R : ℝ, 1 ≤ R → |c| ≤ R →
      IntervalC2Bound (fun u => (Real.smoothTransition (c * u ^ 2 + d) : ℂ))
        (1 / 4) 1 M R := by
  obtain ⟨A, hA, hfirst⟩ := exists_norm_iteratedDeriv_smoothTransition_le 1
  obtain ⟨B, hB, hsecond⟩ := exists_norm_iteratedDeriv_smoothTransition_le 2
  let M : ℝ := 1 + 4 * A + 4 * B
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro c d R hR hc
  have hR0 : 0 ≤ R := by linarith
  have hs : ContDiff ℝ 2 (fun u => Real.smoothTransition (c * u ^ 2 + d)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hpow (u : ℝ) (hu : u ∈ Icc (1 / 4 : ℝ) 1) : |2 * c * u| ≤ 2 * R := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by linarith [hu.1] : 0 ≤ u)]
    have h := mul_le_mul hc hu.2 (by linarith [hu.1]) hR0
    nlinarith
  refine ⟨hM.le, hR0, fun _ _ => (Complex.ofRealCLM.contDiff.comp hs).contDiffAt,
    ?_, ?_, ?_⟩
  · intro u hu
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (Real.smoothTransition.le_one _).trans (by dsimp [M]; nlinarith)
  · intro u hu
    have he := iteratedDeriv_ofReal_fun ((hs.of_le (by norm_num :
      (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := u))
    simp only [iteratedDeriv_one] at he
    rw [he, Complex.norm_real, deriv_smoothTransition_quadratic, Real.norm_eq_abs, abs_mul]
    have hb : |deriv Real.smoothTransition (c * u ^ 2 + d)| ≤ A := by
      simpa only [iteratedDeriv_one, Real.norm_eq_abs] using hfirst (c * u ^ 2 + d)
    calc
      _ ≤ (2 * R) * A := mul_le_mul (hpow u hu) hb (abs_nonneg _) (by positivity)
      _ ≤ M * R := by dsimp [M]; nlinarith
  · intro u hu
    have he := iteratedDeriv_ofReal_fun (hs.contDiffAt (x := u))
    rw [he, Complex.norm_real, iteratedDeriv_two_smoothTransition_quadratic,
      Real.norm_eq_abs]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_pow, abs_mul (2 : ℝ) c,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hb1 : |deriv Real.smoothTransition (c * u ^ 2 + d)| ≤ A := by
      simpa only [iteratedDeriv_one, Real.norm_eq_abs] using hfirst (c * u ^ 2 + d)
    have hb2 : |iteratedDeriv 2 Real.smoothTransition (c * u ^ 2 + d)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hsecond (c * u ^ 2 + d)
    calc
      _ ≤ (2 * R) ^ 2 * B + (2 * R) * A := by
        exact add_le_add
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hpow u hu) 2) hb2
            (abs_nonneg _) (by positivity))
          (mul_le_mul (by nlinarith : 2 * |c| ≤ 2 * R) hb1 (abs_nonneg _) (by positivity))
      _ ≤ M * R ^ 2 := by dsimp [M]; nlinarith [mul_nonneg hA.le (show 0 ≤ R ^ 2 - R by nlinarith)]

end MathCollab.Density.Stronger.Atkinson
