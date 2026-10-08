module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorMass

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


def zetaDivisorLatticePhase (x : ℝ) : ℂ := Complex.exp ((-2 * Real.pi * x : ℝ) * I)

def zetaAtkinsonDivisorTest (T G L x : ℝ) : ℂ :=
  zetaDivisorLatticePhase x * zetaSmoothDivisorTest T G L x

theorem norm_zetaDivisorLatticePhase (x : ℝ) : ‖zetaDivisorLatticePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem zetaDivisorLatticePhase_nat (n : ℕ) : zetaDivisorLatticePhase n = 1 := by
  unfold zetaDivisorLatticePhase
  rw [show ((-2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * I = -((n : ℂ) * (2 * Real.pi * I)) by
    push_cast
    ring]
  rw [Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one]

theorem contDiff_zetaDivisorLatticePhase : ContDiff ℝ ∞ zetaDivisorLatticePhase := by
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold zetaDivisorLatticePhase
  push_cast
  fun_prop

theorem norm_zetaAtkinsonDivisorTest (T G L x : ℝ) :
    ‖zetaAtkinsonDivisorTest T G L x‖ = ‖zetaSmoothDivisorTest T G L x‖ := by
  rw [zetaAtkinsonDivisorTest, norm_mul, norm_zetaDivisorLatticePhase, one_mul]

theorem zetaAtkinsonDivisorTest_nat (T G L : ℝ) (n : ℕ) :
    zetaAtkinsonDivisorTest T G L n = zetaSmoothDivisorTest T G L n := by
  rw [zetaAtkinsonDivisorTest, zetaDivisorLatticePhase_nat, one_mul]

theorem support_zetaAtkinsonDivisorTest (T G L : ℝ) :
    Function.support (zetaAtkinsonDivisorTest T G L) = Function.support (zetaSmoothDivisorTest T G L) := by
  ext x
  change zetaAtkinsonDivisorTest T G L x ≠ 0 ↔ zetaSmoothDivisorTest T G L x ≠ 0
  rw [← norm_ne_zero_iff, norm_zetaAtkinsonDivisorTest]
  exact norm_ne_zero_iff

theorem contDiff_zetaAtkinsonDivisorTest {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) : ContDiff ℝ ∞ (zetaAtkinsonDivisorTest T G L) :=
  contDiff_zetaDivisorLatticePhase.mul (contDiff_zetaSmoothDivisorTest hT hG hL)

def zetaAtkinsonDivisorVoronoiTest {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    DFIVoronoiTestFunction (zetaAtkinsonDivisorTest T G L) where
  lower := zetaDivisorBandEdge T G (-2 * L)
  upper := zetaDivisorBandEdge T G (2 * L)
  lower_pos := zetaDivisorBandEdge_pos hT G (-2 * L)
  lower_le_upper := (zetaDivisorBandEdge_strictMono hT hG).monotone (by linarith)
  smooth := contDiff_zetaAtkinsonDivisorTest hT hG hL
  support_subset := by
    rw [support_zetaAtkinsonDivisorTest]
    exact support_zetaSmoothDivisorTest hT hG hL

theorem zetaSmoothDivisorSum_eq_atkinson_test (T G L : ℝ) :
    zetaSmoothDivisorSum T G L = ∑' n : ℕ, divisorWeight n * zetaAtkinsonDivisorTest T G L n := by
  apply tsum_congr
  intro n
  rw [zetaAtkinsonDivisorTest_nat]

end MathCollab.Density.Stronger.Atkinson
