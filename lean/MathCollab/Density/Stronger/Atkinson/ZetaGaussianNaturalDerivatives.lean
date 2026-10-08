module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaQuadraticGaussianSecondDerivative
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.Atkinson.DivisorTestSmooth

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Natural Gaussian derivative scale

Retaining frequency damping gives Q'=O(G²) and Q''=O(G³), uniformly
in the real frequency. This is the scale needed to freeze the actual
amplitude near its saddle; the coarser height-scale bounds are not used.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

theorem sq_mul_gaussian_eighth_le (x : ℝ) : x ^ 2 * Real.exp (-x ^ 2 / 8) ≤ 8 := by
  have h := Real.add_one_le_exp (x ^ 2 / 8)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-x ^ 2 / 8)).le
  have he : Real.exp (x ^ 2 / 8) * Real.exp (-x ^ 2 / 8) = 1 := by
    rw [← Real.exp_add, show x ^ 2 / 8 + -x ^ 2 / 8 = 0 by ring, Real.exp_zero]
  rw [he] at hm
  nlinarith [Real.exp_pos (-x ^ 2 / 8)]

theorem abs_mul_gaussian_eighth_le (x : ℝ) : |x| * Real.exp (-x ^ 2 / 8) ≤ 9 := by
  have hs := sq_mul_gaussian_eighth_le x
  have he : Real.exp (-x ^ 2 / 8) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  have h := mul_le_mul_of_nonneg_right hx (Real.exp_pos (-x ^ 2 / 8)).le
  nlinarith

theorem norm_deriv_zetaGaussianQuadraticIntegral_le_natural {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖deriv (zetaGaussianQuadraticIntegral T G) v‖ ≤ 5 * Real.sqrt Real.pi * G ^ 2 := by
  apply (norm_deriv_zetaGaussianQuadraticIntegral_le hT hG hGT v).trans
  calc
    _ = (Real.sqrt Real.pi * G ^ 2 / 2) *
        (|G * v| * Real.exp (-(G * v) ^ 2 / 8)) := by
      rw [abs_mul, abs_of_pos hG]
      ring
    _ ≤ (Real.sqrt Real.pi * G ^ 2 / 2) * 9 :=
      mul_le_mul_of_nonneg_left (abs_mul_gaussian_eighth_le (G * v)) (by positivity)
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg Real.pi, sq_nonneg G]

theorem norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le_natural {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖iteratedDeriv 2 (zetaGaussianQuadraticIntegral T G) v‖ ≤
      3 * Real.sqrt Real.pi * G ^ 3 := by
  have hs := sq_mul_gaussian_eighth_le (G * v)
  have he : Real.exp (-(G * v) ^ 2 / 8) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (G * v)])
  have hb : (G * v) ^ 2 * Real.exp (-(G * v) ^ 2 / 8) / 4 +
      Real.exp (-(G * v) ^ 2 / 8) / 2 ≤ 3 := by linarith
  apply (norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le hT hG hGT v).trans
  calc
    _ = (Real.sqrt Real.pi * G ^ 3) *
        ((G * v) ^ 2 * Real.exp (-(G * v) ^ 2 / 8) / 4 +
          Real.exp (-(G * v) ^ 2 / 8) / 2) := by ring
    _ ≤ (Real.sqrt Real.pi * G ^ 3) * 3 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem exists_intervalC2Bound_quadraticGaussian_profile_natural {v : ℝ → ℝ} {a b : ℝ}
    (hv : ∀ u ∈ Icc a b, ContDiffAt ℝ 2 v u) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      IntervalC2Bound (fun u => zetaGaussianQuadraticIntegral T G (v u)) a b (C * G) G := by
  obtain ⟨M, hM, hprofile⟩ := exists_real_profile_derivative_bound hv
  let A : ℝ := 1 + 5 * M + 3 * M ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hA0 : 1 ≤ A := by dsimp [A]; nlinarith
  have hA1 : 5 * M ≤ A := by dsimp [A]; nlinarith
  have hA2 : 3 * M ^ 2 + 5 * M ≤ A := by dsimp [A]; linarith
  refine ⟨Real.sqrt Real.pi * A, by positivity, ?_⟩
  intro T G hT hG hGT
  have hG0 : 0 < G := by linarith
  have hQ : ContDiff ℝ 2 (zetaGaussianQuadraticIntegral T G) :=
    (contDiff_zetaGaussianQuadraticIntegral T hG0.ne').of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))
  refine ⟨by positivity, hG0.le, fun u hu => hQ.contDiffAt.comp u (hv u hu), ?_, ?_, ?_⟩
  · intro u hu
    apply (norm_zetaGaussianQuadraticIntegral_le_mass hT hG0 hGT (v u)).trans
    have h := mul_le_mul_of_nonneg_right hA0 (show 0 ≤ Real.sqrt Real.pi * G by positivity)
    nlinarith
  · intro u hu
    have hd : HasDerivAt (fun w => zetaGaussianQuadraticIntegral T G (v w))
        (deriv v u • deriv (zetaGaussianQuadraticIntegral T G) (v u)) u :=
      (hQ.differentiable (by norm_num)).differentiableAt.hasDerivAt.scomp
        (h := v) u ((hv u hu).differentiableAt (by norm_num)).hasDerivAt
    rw [hd.deriv, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ M * (5 * Real.sqrt Real.pi * G ^ 2) :=
        mul_le_mul (hprofile u hu).2.1
          (norm_deriv_zetaGaussianQuadraticIntegral_le_natural hT hG0 hGT (v u))
          (norm_nonneg _) hM.le
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hA1 (show 0 ≤ Real.sqrt Real.pi * G ^ 2 by positivity)
        nlinarith
  · intro u hu
    rw [iteratedDeriv_two_comp_real hQ.contDiffAt (hv u hu)]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
    have hs := pow_le_pow_left₀ (abs_nonneg (deriv v u)) (hprofile u hu).2.1 2
    rw [sq_abs] at hs
    calc
      _ ≤ M ^ 2 * (3 * Real.sqrt Real.pi * G ^ 3) + M * (5 * Real.sqrt Real.pi * G ^ 2) :=
        add_le_add
          (mul_le_mul hs (norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le_natural hT hG0 hGT (v u))
            (norm_nonneg _) (sq_nonneg M))
          (mul_le_mul (hprofile u hu).2.2 (norm_deriv_zetaGaussianQuadraticIntegral_le_natural hT hG0 hGT (v u))
            (norm_nonneg _) hM.le)
      _ ≤ (3 * M ^ 2 + 5 * M) * (Real.sqrt Real.pi * G ^ 3) := by
        have h := mul_le_mul_of_nonneg_left (show G ^ 2 ≤ G ^ 3 by nlinarith [sq_nonneg (G - 1)])
          (show 0 ≤ 5 * M * Real.sqrt Real.pi by positivity)
        nlinarith
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hA2 (show 0 ≤ Real.sqrt Real.pi * G ^ 3 by positivity)
        nlinarith

end MathCollab.Density.Stronger.Atkinson
