module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.ShortDivisorSource

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := x)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hx1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx] at h
  have hle := (le_abs_self (Real.exp x - 1 - x)).trans h
  nlinarith

theorem zetaQuadraticDivisorBand_abs_sub_center_le {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 ≤ L) (hLG : L ≤ G)
    {n : ℕ} (hn : n ∈ zetaQuadraticDivisorBand T G L) :
    |(n : ℝ) - T / (2 * Real.pi)| ≤ 2 * (T / (2 * Real.pi)) * (L / G) := by
  have hA : 0 < T / (2 * Real.pi) := by positivity
  have hratio0 : 0 ≤ L / G := by positivity
  have hratio1 : L / G ≤ 1 := (div_le_one hG).mpr hLG
  have hbounds := zetaQuadraticDivisorBand_index_bounds hT hG hn
  have hu := mul_le_mul_of_nonneg_left
    (exp_sub_one_le_two_mul hratio0 hratio1) hA.le
  have hl := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(L / G))) hA.le
  rw [neg_div] at hbounds
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A single threshold works for all widths above the source lower scale.
The physical support has length `O(T log T/G)` and stays at indices
comparable with `T`, with every endpoint included. -/
theorem exists_zetaQuadraticDivisorBand_physical_bounds {δ : ℝ} (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → T ^ δ ≤ G →
      ∀ n ∈ zetaQuadraticDivisorBand T G (Real.log T),
        |(n : ℝ) - T / (2 * Real.pi)| ≤ T * Real.log T / (Real.pi * G) ∧
          T / (4 * Real.pi) ≤ (n : ℝ) ∧ (n : ℝ) ≤ T / Real.pi := by
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G →
      ∀ n ∈ zetaQuadraticDivisorBand T G (Real.log T),
        |(n : ℝ) - T / (2 * Real.pi)| ≤ T * Real.log T / (Real.pi * G) ∧
          T / (4 * Real.pi) ≤ (n : ℝ) ∧ (n : ℝ) ≤ T / Real.pi := by
    filter_upwards [eventually_const_log_pow_le_rpow 4 (by norm_num) 1 hδ,
      eventually_ge_atTop (8 : ℝ)] with T hlog hT
    intro G hGscale n hn
    have hT0 : 0 < T := by linarith
    have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hGscale
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    simp only [pow_one] at hlog
    have h4log : 4 * Real.log T ≤ G := hlog.trans hGscale
    have hbound := zetaQuadraticDivisorBand_abs_sub_center_le hT0 hG hlog0 (by linarith) hn
    have hratio : Real.log T / G ≤ 1 / 4 := by
      apply (div_le_iff₀ hG).mpr
      linarith
    have hhalf : 2 * (T / (2 * Real.pi)) * (Real.log T / G) ≤ T / (4 * Real.pi) := by
      calc
        _ ≤ 2 * (T / (2 * Real.pi)) * (1 / 4) := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by ring
    have hlo := (abs_le.mp (hbound.trans hhalf)).1
    have hup := (abs_le.mp (hbound.trans hhalf)).2
    refine ⟨?_, ?_, ?_⟩
    · convert hbound using 1
      ring
    · have hcenter : T / (2 * Real.pi) = 2 * (T / (4 * Real.pi)) := by ring
      rw [hcenter] at hlo
      linarith
    · have hcenter : T / (2 * Real.pi) = 2 * (T / (4 * Real.pi)) := by ring
      have htotal : T / Real.pi = 4 * (T / (4 * Real.pi)) := by ring
      rw [hcenter] at hup
      rw [htotal]
      linarith [show 0 ≤ T / (4 * Real.pi) by positivity]
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨max 8 T₁, le_max_left _ _, ?_⟩
  intro T G hT hG
  exact hT₁ T ((le_max_right _ _).trans hT) G hG

def zetaShortDivisorTestFunction (T G x : ℝ) : ℂ :=
  (x : ℂ) ^ ((-1 / 2 : ℂ) + (T : ℂ) * I) *
    zetaDivisorWeight ((Real.log x : ℂ) - zetaGammaLeadingLog T) *
    zetaSquareReflectedGammaPhase T *
    zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem zetaQuadraticDivisorTerm_eq_testFunction (T G : ℝ) (n : ℕ) :
    zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))) =
      divisorWeight n * zetaShortDivisorTestFunction T G n := by
  have hs : -afeCriticalPoint (-T) = (-1 / 2 : ℂ) + (T : ℂ) * I := by
    unfold afeCriticalPoint
    push_cast
    ring
  simp only [zetaFrozenDivisorCoefficient, divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    hs, zetaShortDivisorTestFunction, zetaDivisorWeightArgument, Complex.ofReal_natCast]
  ring

theorem zetaShortQuadraticDivisorSum_eq_divisor_test (T G L : ℝ) :
    zetaShortQuadraticDivisorSum T G L =
      ∑ n ∈ zetaQuadraticDivisorBand T G L, divisorWeight n * zetaShortDivisorTestFunction T G n := by
  unfold zetaShortQuadraticDivisorSum
  exact Finset.sum_congr rfl (fun n _ => zetaQuadraticDivisorTerm_eq_testFunction T G n)

end MathCollab.Density.Stronger.Atkinson
