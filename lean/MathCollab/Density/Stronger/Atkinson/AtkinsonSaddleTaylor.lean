module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quantitative quadratic remainder at the actual root saddle

The cubic error is derived from the true logarithm, with no supplied
stationary-phase estimate. It controls the actual oscillatory kernel locally.
-/

noncomputable section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

theorem abs_log_one_add_sub_quadratic_le {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) - z + z ^ 2 / 2| ≤ 2 * |z| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -z)
    (by rw [abs_neg]; linarith) 2
  norm_num [Finset.sum_range_succ] at h
  have he : -z + z ^ 2 / 2 + Real.log (1 + z) = Real.log (1 + z) - z + z ^ 2 / 2 := by ring
  rw [he] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - |z|)).2
  have hp : 0 ≤ |z| ^ 3 := by positivity
  nlinarith

def atkinsonRootQuadratic (T b y : ℝ) : ℝ :=
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  atkinsonRootPhase T b r - (1 + (T / (2 * Real.pi)) / r ^ 2) * (y - r) ^ 2

theorem atkinsonRootPhase_sub_quadratic {T y : ℝ} (hT : 0 < T) (hy : 0 < y) (b : ℝ) :
    atkinsonRootPhase T b y - atkinsonRootQuadratic T b y =
      (T / Real.pi) * (Real.log (1 + (y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
        atkinsonSaddleRoot (T / (2 * Real.pi)) b) -
          (y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
            atkinsonSaddleRoot (T / (2 * Real.pi)) b +
              ((y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
                atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2 / 2) := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have he : r ^ 2 - b * r = T / (2 * Real.pi) := atkinsonSaddleRoot_equation (by positivity) b
  have hlog : Real.log y = Real.log r + Real.log (1 + (y - r) / r) := by
    rw [show 1 + (y - r) / r = y / r by field_simp; ring,
      Real.log_div hy.ne' hr.ne']
    ring
  change atkinsonRootPhase T b y -
    (atkinsonRootPhase T b r - (1 + (T / (2 * Real.pi)) / r ^ 2) * (y - r) ^ 2) = _
  change _ = (T / Real.pi) * (Real.log (1 + (y - r) / r) - (y - r) / r + ((y - r) / r) ^ 2 / 2)
  unfold atkinsonRootPhase
  rw [hlog, show T / Real.pi = 2 * (T / (2 * Real.pi)) by ring, ← he]
  field_simp
  ring

theorem abs_atkinsonRootPhase_sub_quadratic_le {T y : ℝ} (hT : 0 < T) (b : ℝ)
    (hy : |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ≤
      atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    |atkinsonRootPhase T b y - atkinsonRootQuadratic T b y| ≤
      2 * T * |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ^ 3 /
        (Real.pi * (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T / (2 * Real.pi)) b
  have hy0 : 0 < y := by linarith [(abs_le.mp hy).1]
  have hz : |(y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
      atkinsonSaddleRoot (T / (2 * Real.pi)) b| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hr).2
    linarith
  rw [atkinsonRootPhase_sub_quadratic hT hy0 b, abs_mul,
    abs_of_pos (div_pos hT Real.pi_pos)]
  apply (mul_le_mul_of_nonneg_left (abs_log_one_add_sub_quadratic_le hz)
    (div_pos hT Real.pi_pos).le).trans_eq
  rw [abs_div, abs_of_pos hr]
  ring

theorem norm_exp_real_phase_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have he : Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I) =
      Complex.exp ((b : ℂ) * I) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, show ‖Complex.exp ((b : ℂ) * I)‖ = 1 by simp [Complex.norm_exp], one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem norm_atkinsonRootKernel_sub_quadratic_le {T y : ℝ} (hT : 0 < T) (b : ℝ)
    (hy : |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ≤
      atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    ‖atkinsonRootKernel T b y - Complex.exp
      (((2 * Real.pi * atkinsonRootQuadratic T b y : ℝ) : ℂ) * I)‖ ≤
      4 * T * |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ^ 3 /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3 := by
  have he : atkinsonRootKernel T b y =
      Complex.exp (((2 * Real.pi * atkinsonRootPhase T b y : ℝ) : ℂ) * I) := by
    unfold atkinsonRootKernel
    congr 1
    push_cast
    ring
  rw [he]
  apply (norm_exp_real_phase_sub_le _ _).trans
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply (mul_le_mul_of_nonneg_left (abs_atkinsonRootPhase_sub_quadratic_le hT b hy)
    (show 0 ≤ 2 * Real.pi by positivity)).trans_eq
  field_simp
  ring

end MathCollab.Density.Stronger.Atkinson
