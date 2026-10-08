module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.FrozenDivisorGaussian

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


open Classical in
def zetaQuadraticDivisorBand (T G L : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil (T / (2 * Real.pi) * Real.exp (L / G)) + 1)).filter
    (fun n => 0 < n ∧ G * |Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))| ≤ L)

def zetaShortQuadraticDivisorSum (T G L : ℝ) : ℂ :=
  ∑ n ∈ zetaQuadraticDivisorBand T G L,
    zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))

theorem divisor_index_bounds_of_frequency {T G L : ℝ} (hT : 0 < T) (hG : 0 < G)
    {n : ℕ} (hn : 0 < n)
    (hfreq : G * |Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))| ≤ L) :
    T / (2 * Real.pi) * Real.exp (-L / G) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ T / (2 * Real.pi) * Real.exp (L / G) := by
  have ha : 0 < T / (2 * Real.pi) := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : |Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))| ≤ L / G :=
    (le_div_iff₀ hG).mpr (by simpa only [mul_comm] using hfreq)
  have hlog := abs_le.mp habs
  constructor
  · have h := Real.exp_le_exp.mpr (show Real.log (T / (2 * Real.pi)) + -L / G ≤
        Real.log (n : ℝ) by rw [neg_div]; linarith)
    simpa only [Real.exp_add, Real.exp_log ha, Real.exp_log hn0] using h
  · have h := Real.exp_le_exp.mpr (show Real.log (n : ℝ) ≤
        Real.log (T / (2 * Real.pi)) + L / G by linarith)
    simpa only [Real.exp_add, Real.exp_log ha, Real.exp_log hn0] using h

theorem mem_zetaQuadraticDivisorBand_iff {T G L : ℝ} (hT : 0 < T) (hG : 0 < G) (n : ℕ) :
    n ∈ zetaQuadraticDivisorBand T G L ↔
      0 < n ∧ G * |Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))| ≤ L := by
  classical
  rw [zetaQuadraticDivisorBand, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ?_), h⟩
    exact_mod_cast (divisor_index_bounds_of_frequency hT hG h.1 h.2).2.trans (Nat.le_ceil _)

theorem zero_not_mem_zetaQuadraticDivisorBand (T G L : ℝ) :
    0 ∉ zetaQuadraticDivisorBand T G L := by
  classical
  simp [zetaQuadraticDivisorBand]

theorem zetaQuadraticDivisorBand_index_bounds {T G L : ℝ} (hT : 0 < T) (hG : 0 < G)
    {n : ℕ} (hn : n ∈ zetaQuadraticDivisorBand T G L) :
    T / (2 * Real.pi) * Real.exp (-L / G) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ T / (2 * Real.pi) * Real.exp (L / G) := by
  have h := (mem_zetaQuadraticDivisorBand_iff hT hG n).mp hn
  exact divisor_index_bounds_of_frequency hT hG h.1 h.2

theorem frequency_le_of_not_mem_zetaQuadraticDivisorBand {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) {n : ℕ} (hn : 0 < n)
    (hnot : n ∉ zetaQuadraticDivisorBand T G L) :
    L ≤ G * |Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))| := by
  have h := mt (mem_zetaQuadraticDivisorBand_iff hT hG n).mpr hnot
  exact (lt_of_not_ge (fun hfreq => h ⟨hn, hfreq⟩)).le

theorem zetaFrozenDivisorCoefficient_zero (T : ℝ) : zetaFrozenDivisorCoefficient T 0 = 0 := by
  simp [zetaFrozenDivisorCoefficient, divisorDirichletTerm, LSeries.term]

theorem norm_zetaQuadraticDivisorTerm_off_band_le {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 ≤ L)
    {n : ℕ} (hnot : n ∉ zetaQuadraticDivisorBand T G L) :
    ‖zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))‖ ≤
      ‖zetaFrozenDivisorCoefficient T n‖ *
        (Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) := by
  by_cases hn : n = 0
  · simp [hn, zetaFrozenDivisorCoefficient_zero]
  rw [norm_mul, norm_mul, norm_zetaSquareReflectedGammaPhase, mul_one]
  exact mul_le_mul_of_nonneg_left (norm_zetaGaussianQuadraticIntegral_tail hT hG hGT hL
    (frequency_le_of_not_mem_zetaQuadraticDivisorBand hT hG (Nat.pos_of_ne_zero hn) hnot)) (norm_nonneg _)

end MathCollab.Density.Stronger.Atkinson
