module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonPhase

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Unique nondegenerate saddle of the actual source carrier

The same real parameter b covers zero (the logarithmic main term)
and the two prospective Bessel carriers sqrt(n) and -sqrt(n).
A is the normalized height; the consumer substitutes T/(2*pi).
These exact calculus statements are not a stationary-phase estimate.
-/

noncomputable section

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSaddleRoot (A b : ℝ) : ℝ := (b + Real.sqrt (b ^ 2 + 4 * A)) / 2

def zetaAtkinsonSaddle (T b : ℝ) : ℝ := (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2

theorem atkinsonSaddleRoot_pos {A : ℝ} (hA : 0 < A) (b : ℝ) :
    0 < atkinsonSaddleRoot A b := by
  have h := Real.sqrt_lt_sqrt (sq_nonneg b) (show b ^ 2 < b ^ 2 + 4 * A by linarith)
  rw [Real.sqrt_sq_eq_abs] at h
  unfold atkinsonSaddleRoot
  linarith [neg_abs_le b]

theorem atkinsonSaddleRoot_equation {A : ℝ} (hA : 0 < A) (b : ℝ) :
    (atkinsonSaddleRoot A b) ^ 2 - b * atkinsonSaddleRoot A b = A := by
  have hs := Real.sq_sqrt (show 0 ≤ b ^ 2 + 4 * A by positivity)
  unfold atkinsonSaddleRoot
  nlinarith

theorem atkinsonSaddleRoot_sub_pos {A : ℝ} (hA : 0 < A) (b : ℝ) :
    0 < atkinsonSaddleRoot A b - b := by
  have hmul : 0 < atkinsonSaddleRoot A b * (atkinsonSaddleRoot A b - b) := by
    nlinarith [atkinsonSaddleRoot_equation hA b]
  exact (mul_pos_iff.mp hmul).resolve_right (fun h => (atkinsonSaddleRoot_pos hA b).not_gt h.1) |>.2

theorem atkinson_saddle_equation_iff {A x : ℝ} (hA : 0 < A) (hx : 0 < x) (b : ℝ) :
    x - b * Real.sqrt x = A ↔ x = (atkinsonSaddleRoot A b) ^ 2 := by
  have hr := atkinsonSaddleRoot_pos hA b
  have he := atkinsonSaddleRoot_equation hA b
  constructor
  · intro h
    have hf : (Real.sqrt x - atkinsonSaddleRoot A b) *
        (Real.sqrt x + atkinsonSaddleRoot A b - b) = 0 := by
      nlinarith [Real.sq_sqrt hx.le]
    have hp : 0 < Real.sqrt x + atkinsonSaddleRoot A b - b := by
      linarith [Real.sqrt_nonneg x, atkinsonSaddleRoot_sub_pos hA b]
    have heq := (mul_eq_zero.mp hf).resolve_right hp.ne'
    nlinarith [Real.sq_sqrt hx.le]
  · rintro rfl
    rw [Real.sqrt_sq hr.le]
    exact he

theorem zetaAtkinsonSaddle_pos {T : ℝ} (hT : 0 < T) (b : ℝ) :
    0 < zetaAtkinsonSaddle T b :=
  sq_pos_of_pos (atkinsonSaddleRoot_pos (by positivity : 0 < T / (2 * Real.pi)) b)

theorem zetaAtkinsonPhase_deriv_factored (T b : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (zetaAtkinsonPhase T b) x =
      (2 * Real.pi / x) * (T / (2 * Real.pi) - (x - b * Real.sqrt x)) := by
  rw [(hasDerivAt_zetaAtkinsonPhase T b hx).deriv]
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hf : b / Real.sqrt x = b * Real.sqrt x / x := by
    field_simp
    rw [Real.sq_sqrt hx.le]
  rw [show 2 * Real.pi * b / Real.sqrt x = 2 * Real.pi * (b / Real.sqrt x) by ring, hf]
  field_simp
  ring

theorem zetaAtkinsonPhase_stationary_iff {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (b : ℝ) :
    deriv (zetaAtkinsonPhase T b) x = 0 ↔ x = zetaAtkinsonSaddle T b := by
  rw [zetaAtkinsonPhase_deriv_factored T b hx, mul_eq_zero]
  have hp : 2 * Real.pi / x ≠ 0 := ne_of_gt (by positivity : 0 < 2 * Real.pi / x)
  simp only [hp, false_or, sub_eq_zero]
  rw [eq_comm, atkinson_saddle_equation_iff (by positivity : 0 < T / (2 * Real.pi)) hx b]
  rfl

theorem zetaAtkinsonPhase_stationary {T : ℝ} (hT : 0 < T) (b : ℝ) :
    deriv (zetaAtkinsonPhase T b) (zetaAtkinsonSaddle T b) = 0 :=
  (zetaAtkinsonPhase_stationary_iff hT (zetaAtkinsonSaddle_pos hT b) b).mpr rfl

theorem zetaAtkinsonSaddle_zero {T : ℝ} (hT : 0 < T) :
    zetaAtkinsonSaddle T 0 = T / (2 * Real.pi) := by
  have h := atkinsonSaddleRoot_equation (by positivity : 0 < T / (2 * Real.pi)) 0
  simpa only [zero_mul, sub_zero, zetaAtkinsonSaddle] using h


theorem zetaAtkinsonPhase_secondDeriv_saddle {T : ℝ} (hT : 0 < T) (b : ℝ) :
    deriv (deriv (zetaAtkinsonPhase T b)) (zetaAtkinsonSaddle T b) =
      -Real.pi * (2 * atkinsonSaddleRoot (T / (2 * Real.pi)) b - b) /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3 := by
  have hA : 0 < T / (2 * Real.pi) := by positivity
  have hr := atkinsonSaddleRoot_pos hA b
  have he := atkinsonSaddleRoot_equation hA b
  have hTval : ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2 -
      b * atkinsonSaddleRoot (T / (2 * Real.pi)) b) * (2 * Real.pi) = T :=
    (eq_div_iff (by positivity : 2 * Real.pi ≠ 0)).mp he
  rw [(hasDerivAt_deriv_zetaAtkinsonPhase T b (zetaAtkinsonSaddle_pos hT b)).deriv]
  simp only [zetaAtkinsonSaddle, Real.sqrt_sq hr.le]
  generalize atkinsonSaddleRoot (T / (2 * Real.pi)) b = r at *
  rw [← hTval]
  field_simp
  ring

theorem zetaAtkinsonPhase_secondDeriv_saddle_neg {T : ℝ} (hT : 0 < T) (b : ℝ) :
    deriv (deriv (zetaAtkinsonPhase T b)) (zetaAtkinsonSaddle T b) < 0 := by
  rw [zetaAtkinsonPhase_secondDeriv_saddle hT b]
  have hA : 0 < T / (2 * Real.pi) := by positivity
  have hr := atkinsonSaddleRoot_pos hA b
  have hp : 0 < 2 * atkinsonSaddleRoot (T / (2 * Real.pi)) b - b := by
    linarith [atkinsonSaddleRoot_sub_pos hA b]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) hp) (by positivity)

end MathCollab.Density.Stronger.Atkinson
