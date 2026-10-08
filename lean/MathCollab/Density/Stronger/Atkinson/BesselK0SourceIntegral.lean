module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselK0Decay
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorMass
public import Mathlib.MeasureTheory.Integral.Prod

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaBesselK0SourceIntegrand (T G L : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  zetaSmoothDivisorTest T G L x * (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

theorem stronglyMeasurable_dfiBesselK0 : StronglyMeasurable dfiBesselK0 := by
  have h : StronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-p.1 * Real.cosh p.2)) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => Real.exp (-p.1 * Real.cosh p.2))).stronglyMeasurable
  exact h.integral_prod_right' (ν := volume.restrict (Ioi 0))

theorem norm_zetaBesselK0SourceIntegrand_le {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) (k : ℕ) (x : ℝ) :
    ‖zetaBesselK0SourceIntegrand T G L n x‖ ≤
      (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
        ‖zetaSmoothDivisorTest T G L x‖ := by
  by_cases hx : zetaSmoothDivisorTest T G L x = 0
  · simp only [zetaBesselK0SourceIntegrand, hx, zero_mul, norm_zero, mul_zero, le_refl]
  have hs := support_zetaSmoothDivisorTest_physical (by linarith : 0 < T) hG hL hwidth hx
  unfold zetaBesselK0SourceIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖zetaSmoothDivisorTest T G L x‖ *
        (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) :=
      mul_le_mul_of_nonneg_left (abs_dfiBesselK0_source_le hT hs.1 hn k) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem integrable_zetaBesselK0SourceIntegrand {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) : Integrable (zetaBesselK0SourceIntegrand T G L n) := by
  have hm : AEStronglyMeasurable (zetaBesselK0SourceIntegrand T G L n) := by
    have hK : Measurable (fun x : ℝ => (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)) :=
      Complex.measurable_ofReal.comp (stronglyMeasurable_dfiBesselK0.measurable.comp (by fun_prop))
    exact (contDiff_zetaSmoothDivisorTest (by linarith : 0 < T) hG hL).continuous.aestronglyMeasurable.mul
      hK.aestronglyMeasurable
  apply ((integrable_zetaSmoothDivisorTest (by linarith : 0 < T) hG hL).norm.const_mul
    (zetaBesselK0PowerConstant 0 / (T ^ 0 * (n : ℝ) ^ 0))).mono' hm
  exact Filter.Eventually.of_forall (norm_zetaBesselK0SourceIntegrand_le hT hG hL hwidth hn 0)

theorem norm_integral_zetaBesselK0SourceIntegrand_le {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ‖∫ x : ℝ in Ioi 0, zetaBesselK0SourceIntegrand T G L n x‖ ≤
      (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
        ∫ x : ℝ in Ioi 0, ‖zetaSmoothDivisorTest T G L x‖ := by
  have hi : IntegrableOn (fun x : ℝ =>
      (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
        ‖zetaSmoothDivisorTest T G L x‖) (Ioi 0) :=
    ((integrable_zetaSmoothDivisorTest (by linarith : 0 < T) hG hL).norm.integrableOn).const_mul _
  have h := norm_integral_le_of_norm_le hi
    (Filter.Eventually.of_forall (norm_zetaBesselK0SourceIntegrand_le hT hG hL hwidth hn k))
  simpa only [integral_const_mul] using h

theorem exists_norm_integral_zetaBesselK0SourceIntegrand_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ, 0 < n →
      ‖∫ x : ℝ in Ioi 0, zetaBesselK0SourceIntegrand T G L n x‖ ≤
        C * G * T / (T ^ k * (n : ℝ) ^ k) := by
  obtain ⟨C, hC, hmass⟩ := exists_integral_norm_zetaSmoothDivisorTest_le
  refine ⟨zetaBesselK0PowerConstant k * C, mul_pos (zetaBesselK0PowerConstant_pos k) hC, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  apply (norm_integral_zetaBesselK0SourceIntegrand_le hT hG hL hwidth hn k).trans
  have hfac : 0 ≤ zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k) :=
    div_nonneg (zetaBesselK0PowerConstant_pos k).le (by positivity)
  calc
    _ ≤ (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) * (C * G * T) :=
      mul_le_mul_of_nonneg_left (hmass T G L hT hG hGT hL hwidth) hfac
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
