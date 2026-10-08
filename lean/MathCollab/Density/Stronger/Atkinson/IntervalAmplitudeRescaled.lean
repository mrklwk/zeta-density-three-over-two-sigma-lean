module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_intervalC1Bound_rescaled {f : ℝ → ℂ}
    (hf : ∀ x : ℝ, 0 < x → ContDiffAt ℝ 1 f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      IntervalC1Bound (fun x => f (x / T)) (T / 16) T C := by
  have hfc : ContinuousOn f (Icc (1 / 16 : ℝ) 1) :=
    fun x hx => (hf x (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv f) (Icc (1 / 16 : ℝ) 1) := fun x hx =>
    ((hf x (by linarith [hx.1])).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  let C : ℝ := 1 + |M| + |N|
  have hC : 0 < C := by dsimp [C]; positivity
  have hMC : M ≤ C := by dsimp [C]; linarith [le_abs_self M, abs_nonneg N]
  have hNC : N ≤ C := by dsimp [C]; linarith [le_abs_self N, abs_nonneg M]
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hscale (x : ℝ) (hx : x ∈ Icc (T / 16) T) : x / T ∈ Icc (1 / 16 : ℝ) 1 := by
    constructor
    · exact (le_div_iff₀ hT).mpr (by linarith [hx.1])
    · exact (div_le_one hT).mpr hx.2
  have hs (x : ℝ) (hx : x ∈ Icc (T / 16) T) : ContDiffAt ℝ 1 (fun y => f (y / T)) x :=
    (hf (x / T) (by linarith [(hscale x hx).1])).comp x (by fun_prop)
  have hd (x : ℝ) (hx : x ∈ Icc (T / 16) T) :
      deriv (fun y => f (y / T)) x = (1 / T : ℝ) • deriv f (x / T) := by
    exact (((hf (x / T) (by linarith [(hscale x hx).1])).differentiableAt
      (by norm_num)).hasDerivAt.scomp x ((hasDerivAt_id x).div_const T)).deriv
  have hdi : IntervalIntegrable (deriv (fun x => f (x / T))) volume (T / 16) T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : T / 16 ≤ T)]
    intro x hx
    exact ((hs x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨hC.le, hs, fun x hx => (hM (x / T) (hscale x hx)).trans hMC, ?_⟩
  calc
    _ ≤ ∫ x in (T / 16)..T, C / T := by
      apply intervalIntegral.integral_mono_on (by linarith) hdi.norm intervalIntegrable_const
      intro x hx
      rw [hd x hx, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / T)]
      have h := mul_le_mul_of_nonneg_left ((hN (x / T) (hscale x hx)).trans hNC)
        (by positivity : 0 ≤ 1 / T)
      convert h using 1
      ring
    _ = (T - T / 16) * (C / T) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ C := by
      have hfac : 0 ≤ C / T := by positivity
      calc
        _ ≤ T * (C / T) := mul_le_mul_of_nonneg_right (by linarith) hfac
        _ = C := by field_simp

end MathCollab.Density.Stronger.Atkinson
