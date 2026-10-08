module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonSaddle
public import Mathlib.Analysis.SpecialFunctions.Arsinh

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact paired-saddle normalization of the retained source

These identities evaluate the actual saddle positions and source logarithms.
They preserve both signs and precede, rather than assume, stationary evaluation
of the oscillatory integrals. The logarithmic identity is the source counterpart
of Ivić, Topics in Recent Zeta Function Theory, (6.48)--(6.51).
-/

noncomputable section

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonSaddleRoot_neg (A b : ℝ) :
    atkinsonSaddleRoot A (-b) = atkinsonSaddleRoot A b - b := by
  unfold atkinsonSaddleRoot
  rw [neg_sq]
  ring

theorem atkinsonSaddleRoot_mul_neg {A : ℝ} (hA : 0 < A) (b : ℝ) :
    atkinsonSaddleRoot A b * atkinsonSaddleRoot A (-b) = A := by
  rw [atkinsonSaddleRoot_neg]
  nlinarith [atkinsonSaddleRoot_equation hA b]

theorem atkinsonSaddleRoot_sum_neg (A b : ℝ) :
    atkinsonSaddleRoot A b + atkinsonSaddleRoot A (-b) = Real.sqrt (b ^ 2 + 4 * A) := by
  unfold atkinsonSaddleRoot
  rw [neg_sq]
  ring

theorem zetaAtkinsonSaddle_mul_neg {T : ℝ} (hT : 0 < T) (b : ℝ) :
    zetaAtkinsonSaddle T b * zetaAtkinsonSaddle T (-b) = (T / (2 * Real.pi)) ^ 2 := by
  unfold zetaAtkinsonSaddle
  rw [← mul_pow, atkinsonSaddleRoot_mul_neg (by positivity) b]

theorem log_atkinsonSaddleRoot_div_sqrt {A : ℝ} (hA : 0 < A) (b : ℝ) :
    Real.log (atkinsonSaddleRoot A b / Real.sqrt A) = Real.arsinh (b / (2 * Real.sqrt A)) := by
  let r := atkinsonSaddleRoot A b
  have hr : 0 < r := atkinsonSaddleRoot_pos hA b
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have he : r ^ 2 - b * r = A := atkinsonSaddleRoot_equation hA b
  have hratio : 0 < r / Real.sqrt A := by positivity
  have hh : Real.sinh (Real.log (r / Real.sqrt A)) = b / (2 * Real.sqrt A) := by
    rw [Real.sinh_eq, Real.exp_log hratio, Real.exp_neg, Real.exp_log hratio]
    field_simp
    nlinarith [Real.sq_sqrt hA.le]
  have h := congrArg Real.arsinh hh
  simpa only [Real.arsinh_sinh] using h

theorem log_atkinsonSaddleRoot_sq_sub_log {A : ℝ} (hA : 0 < A) (b : ℝ) :
    Real.log ((atkinsonSaddleRoot A b) ^ 2) - Real.log A =
      2 * Real.arsinh (b / (2 * Real.sqrt A)) := by
  have h := log_atkinsonSaddleRoot_div_sqrt hA b
  rw [Real.log_div (atkinsonSaddleRoot_pos hA b).ne'
    (Real.sqrt_pos.2 hA).ne', Real.log_sqrt hA.le] at h
  rw [Real.log_pow]
  linarith

theorem zetaAtkinsonSaddle_log_argument {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Real.log (zetaAtkinsonSaddle T b) - Real.log (T / (2 * Real.pi)) =
      2 * Real.arsinh (b / (2 * Real.sqrt (T / (2 * Real.pi)))) :=
  log_atkinsonSaddleRoot_sq_sub_log (by positivity) b

def atkinsonDualPhase (T b : ℝ) : ℝ :=
  2 * T * Real.arsinh (b / (2 * Real.sqrt (T / (2 * Real.pi)))) +
    Real.pi * b * Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi)))

def atkinsonCentralPhase (T : ℝ) : ℝ := T * Real.log (T / (2 * Real.pi)) - T

theorem atkinsonDualPhase_neg (T b : ℝ) : atkinsonDualPhase T (-b) = -atkinsonDualPhase T b := by
  unfold atkinsonDualPhase
  rw [neg_div, Real.arsinh_neg, neg_sq]
  ring

theorem zetaAtkinsonPhase_at_saddle {T : ℝ} (hT : 0 < T) (b : ℝ) :
    zetaAtkinsonPhase T b (zetaAtkinsonSaddle T b) =
      atkinsonCentralPhase T + Real.pi * b ^ 2 + atkinsonDualPhase T b := by
  have hA : 0 < T / (2 * Real.pi) := by positivity
  have hr := atkinsonSaddleRoot_pos hA b
  have he := atkinsonSaddleRoot_equation hA b
  have hTval := (eq_div_iff (show 2 * Real.pi ≠ 0 by positivity)).mp he
  have hl := zetaAtkinsonSaddle_log_argument hT b
  have hs : Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi))) =
      2 * atkinsonSaddleRoot (T / (2 * Real.pi)) b - b := by
    unfold atkinsonSaddleRoot
    ring
  unfold zetaAtkinsonPhase atkinsonCentralPhase atkinsonDualPhase
  rw [show Real.log (zetaAtkinsonSaddle T b) =
    Real.log (T / (2 * Real.pi)) +
      2 * Real.arsinh (b / (2 * Real.sqrt (T / (2 * Real.pi)))) by linarith,
    zetaAtkinsonSaddle, Real.sqrt_sq hr.le, hs]
  nlinarith

end MathCollab.Density.Stronger.Atkinson
