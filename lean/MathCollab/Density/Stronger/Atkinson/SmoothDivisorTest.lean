module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorTestSmooth
public import MathCollab.Density.Stronger.Atkinson.DivisorBandCutoff
public import MathCollab.Density.Stronger.Atkinson.VoronoiTest

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


def zetaSmoothDivisorTest (T G L x : ℝ) : ℂ :=
  (zetaDivisorBandCutoff T G L x : ℂ) * zetaShortDivisorTestFunction T G x

def zetaSmoothDivisorSum (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * zetaSmoothDivisorTest T G L n

theorem zetaSmoothDivisorTest_eq_zero_left {T G L x : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L)
    (hx : x ≤ zetaDivisorBandEdge T G (-2 * L)) : zetaSmoothDivisorTest T G L x = 0 := by
  have hm := zetaDivisorBandEdge_strictMono hT hG
  have hcut : zetaDivisorBandCutoff T G L x = 0 :=
    zetaBandCutoff_eq_zero_left (hm (by linarith)) hx
  simp only [zetaSmoothDivisorTest, hcut, Complex.ofReal_zero, zero_mul]

theorem support_zetaSmoothDivisorTest {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    Function.support (zetaSmoothDivisorTest T G L) ⊆
      Icc (zetaDivisorBandEdge T G (-2 * L)) (zetaDivisorBandEdge T G (2 * L)) := by
  intro x hx
  apply support_zetaDivisorBandCutoff hT hG hL
  intro hzero
  exact hx (by simp only [zetaSmoothDivisorTest, hzero, Complex.ofReal_zero, zero_mul])

theorem contDiff_zetaSmoothDivisorTest {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    ContDiff ℝ ∞ (zetaSmoothDivisorTest T G L) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · exact ((Complex.ofRealCLM.contDiff.comp (contDiff_zetaDivisorBandCutoff T G L)).contDiffAt).mul
      (contDiffAt_zetaShortDivisorTestFunction T hG.ne' hx)
  · have hxa : x < zetaDivisorBandEdge T G (-2 * L) :=
      (le_of_not_gt hx).trans_lt (zetaDivisorBandEdge_pos hT G (-2 * L))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hxa] with y hy
    exact zetaSmoothDivisorTest_eq_zero_left hT hG hL hy.le

def zetaSmoothDivisorVoronoiTest {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    DFIVoronoiTestFunction (zetaSmoothDivisorTest T G L) where
  lower := zetaDivisorBandEdge T G (-2 * L)
  upper := zetaDivisorBandEdge T G (2 * L)
  lower_pos := zetaDivisorBandEdge_pos hT G (-2 * L)
  lower_le_upper := (zetaDivisorBandEdge_strictMono hT hG).monotone (by linarith)
  smooth := contDiff_zetaSmoothDivisorTest hT hG hL
  support_subset := support_zetaSmoothDivisorTest hT hG hL

theorem zetaSmoothDivisorTerm_eq_cutoff (T G L : ℝ) (n : ℕ) :
    divisorWeight n * zetaSmoothDivisorTest T G L n =
      (zetaDivisorBandCutoff T G L n : ℂ) *
        (zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
          zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))) := by
  rw [zetaQuadraticDivisorTerm_eq_testFunction]
  unfold zetaSmoothDivisorTest
  ring

theorem norm_zetaSmoothDivisorTerm_le (T G L : ℝ) (n : ℕ) :
    ‖divisorWeight n * zetaSmoothDivisorTest T G L n‖ ≤
      ‖zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi)))‖ := by
  rw [zetaSmoothDivisorTerm_eq_cutoff, norm_mul, Complex.norm_real, Real.norm_eq_abs, zetaDivisorBandCutoff,
    abs_of_nonneg (zetaBandCutoff_nonneg _ _ _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (zetaBandCutoff_le_one _ _ _ _ _)

theorem summable_zetaSmoothDivisorTerm {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (L : ℝ) :
    Summable (fun n : ℕ => divisorWeight n * zetaSmoothDivisorTest T G L n) :=
  Summable.of_norm_bounded (summable_zetaFrozenDivisorQuadraticTerm hT hG hGT).norm
    (norm_zetaSmoothDivisorTerm_le T G L)

theorem zetaSmoothDivisorTerm_eq_on_band {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L)
    {n : ℕ} (hn : n ∈ zetaQuadraticDivisorBand T G L) :
    divisorWeight n * zetaSmoothDivisorTest T G L n =
      zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))) := by
  rw [zetaSmoothDivisorTerm_eq_cutoff, zetaDivisorBandCutoff_eq_one hT hG hL hn,
    Complex.ofReal_one, one_mul]

end MathCollab.Density.Stronger.Atkinson
