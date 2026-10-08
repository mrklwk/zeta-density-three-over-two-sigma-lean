module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonVoronoiTerms
public import MathCollab.Density.Stronger.Atkinson.BesselK0SourceIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_zetaAtkinsonK0_integrand (T G L : ℝ) (n : ℕ) (x : ℝ) :
    ‖zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ =
        ‖zetaBesselK0SourceIntegrand T G L n x‖ := by
  simp only [zetaBesselK0SourceIntegrand, norm_mul, norm_zetaAtkinsonDivisorTest]

theorem integrable_zetaAtkinsonK0_integrand {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun x : ℝ => zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)) := by
  have hi := (integrable_zetaBesselK0SourceIntegrand hT hG hL hwidth hn).bdd_mul
    contDiff_zetaDivisorLatticePhase.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (norm_zetaDivisorLatticePhase x).le))
  convert hi using 1
  ext x
  simp only [zetaAtkinsonDivisorTest, zetaBesselK0SourceIntegrand, mul_assoc]

theorem norm_integral_zetaAtkinsonK0_le {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ‖∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ ≤
        (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
          ∫ x : ℝ in Ioi 0, ‖zetaSmoothDivisorTest T G L x‖ := by
  have hi : IntegrableOn (fun x : ℝ =>
      (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
        ‖zetaSmoothDivisorTest T G L x‖) (Ioi 0) :=
    ((integrable_zetaSmoothDivisorTest (by linarith : 0 < T) hG hL).norm.integrableOn).const_mul _
  have hb (x : ℝ) : ‖zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ ≤
        (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
          ‖zetaSmoothDivisorTest T G L x‖ := by
    rw [norm_zetaAtkinsonK0_integrand]
    exact norm_zetaBesselK0SourceIntegrand_le hT hG hL hwidth hn k x
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
  simpa only [integral_const_mul] using h

theorem exists_norm_integral_zetaAtkinsonK0_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ, 0 < n →
      ‖∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
        (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ ≤
          C * G * T / (T ^ k * (n : ℝ) ^ k) := by
  obtain ⟨C, hC, hmass⟩ := exists_integral_norm_zetaSmoothDivisorTest_le
  refine ⟨zetaBesselK0PowerConstant k * C, mul_pos (zetaBesselK0PowerConstant_pos k) hC, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  apply (norm_integral_zetaAtkinsonK0_le hT hG hL hwidth hn k).trans
  have hfac : 0 ≤ zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k) :=
    div_nonneg (zetaBesselK0PowerConstant_pos k).le (by positivity)
  calc
    _ ≤ (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) * (C * G * T) :=
      mul_le_mul_of_nonneg_left (hmass T G L hT hG hGT hL hwidth) hfac
    _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
