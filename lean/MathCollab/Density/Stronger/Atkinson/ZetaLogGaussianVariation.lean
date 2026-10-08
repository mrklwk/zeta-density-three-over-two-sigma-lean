module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Total variation of the actual logarithmic Gaussian envelope

The envelope increases to its actual center and decreases afterwards.
Its variation is at most two, independent of the Gaussian width;
this will control the complex quadratic transform's derivative.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

def zetaLogGaussianEnvelope (A G x : ℝ) : ℝ :=
  Real.exp (-(G * (Real.log x - Real.log A)) ^ 2 / 8)

theorem zetaLogGaussianEnvelope_bounds (A G x : ℝ) :
    0 ≤ zetaLogGaussianEnvelope A G x ∧ zetaLogGaussianEnvelope A G x ≤ 1 := by
  exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (G * (Real.log x - Real.log A))])⟩

theorem contDiffAt_zetaLogGaussianEnvelope (A G : ℝ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 1 (zetaLogGaussianEnvelope A G) x := by
  have hl : ContDiffAt ℝ 1 Real.log x := Real.contDiffAt_log.mpr hx.ne'
  unfold zetaLogGaussianEnvelope
  fun_prop

theorem hasDerivAt_zetaLogGaussianEnvelope (A G : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaLogGaussianEnvelope A G)
      (-(G ^ 2 / 4) * ((Real.log x - Real.log A) / x) * zetaLogGaussianEnvelope A G x) x := by
  have h := ((((Real.hasDerivAt_log hx.ne').sub_const (Real.log A)).const_mul G).pow 2).neg.div_const 8
  convert h.exp using 1
  · rfl
  · dsimp [zetaLogGaussianEnvelope]
    norm_num
    ring

theorem intervalC1Bound_zetaLogGaussianEnvelope {a A b : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hAb : A ≤ b) (G : ℝ) :
    IntervalC1Bound (fun x : ℝ => (zetaLogGaussianEnvelope A G x : ℂ)) a b 2 := by
  have hA : 0 < A := ha.trans_le haA
  have hleft := intervalC1Bound_ofReal_of_deriv_nonneg haA (by norm_num : (0 : ℝ) ≤ 1)
    (fun x hx => contDiffAt_zetaLogGaussianEnvelope A G (ha.trans_le hx.1))
    (fun x _ => zetaLogGaussianEnvelope_bounds A G x) (fun x hx => by
      rw [(hasDerivAt_zetaLogGaussianEnvelope A G (ha.trans_le hx.1)).deriv]
      have hv : Real.log x - Real.log A ≤ 0 := sub_nonpos.mpr
        (Real.log_le_log (ha.trans_le hx.1) hx.2)
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity))
        (div_nonpos_of_nonpos_of_nonneg hv (ha.trans_le hx.1).le))
        (zetaLogGaussianEnvelope_bounds A G x).1)
  have hright := intervalC1Bound_ofReal_of_deriv_nonpos hAb (by norm_num : (0 : ℝ) ≤ 1)
    (fun x hx => contDiffAt_zetaLogGaussianEnvelope A G (hA.trans_le hx.1))
    (fun x _ => zetaLogGaussianEnvelope_bounds A G x) (fun x hx => by
      rw [(hasDerivAt_zetaLogGaussianEnvelope A G (hA.trans_le hx.1)).deriv]
      have hv : 0 ≤ Real.log x - Real.log A := sub_nonneg.mpr (Real.log_le_log hA hx.1)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (div_nonneg hv (hA.trans_le hx.1).le))
        (zetaLogGaussianEnvelope_bounds A G x).1)
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hleft.join hright haA hAb

theorem atkinson_center_mem_physical {T : ℝ} (hT : 0 < T) :
    T / (2 * Real.pi) ∈ Icc (T / 16) T := by
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    have h := mul_le_mul_of_nonneg_left Real.pi_le_four (hT.le)
    nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [mul_pos hT Real.pi_pos, mul_lt_mul_of_pos_left Real.pi_gt_three hT]

end MathCollab.Density.Stronger.Atkinson
