module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import Mathlib

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual signed carrier phase and its derivatives

This narrow extraction does not assert a source or amplitude factorization.
Both real signs of the frequency parameter b remain unrestricted.
-/
noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonPhase (T b x : ℝ) : ℝ :=
  T * Real.log x - 2 * Real.pi * x + 4 * Real.pi * b * Real.sqrt x

theorem hasDerivAt_zetaAtkinsonPhase (T b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaAtkinsonPhase T b)
      (T / x - 2 * Real.pi + 2 * Real.pi * b / Real.sqrt x) x := by
  have h := (((Real.hasDerivAt_log hx.ne').const_mul T).sub
    ((hasDerivAt_id x).const_mul (2 * Real.pi))).add
      ((Real.hasDerivAt_sqrt hx.ne').const_mul (4 * Real.pi * b))
  convert h using 1
  · rfl
  · ring

theorem hasDerivAt_zetaAtkinsonPhaseDerivative (T b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => T / y - 2 * Real.pi + 2 * Real.pi * b / Real.sqrt y)
      (-T / x ^ 2 - Real.pi * b / (Real.sqrt x) ^ 3) x := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have h := (((hasDerivAt_const x T).div (hasDerivAt_id x) hx.ne').sub_const (2 * Real.pi)).add
    ((hasDerivAt_const x (2 * Real.pi * b)).div (Real.hasDerivAt_sqrt hx.ne') hs)
  convert h using 1
  · rfl
  · dsimp [id]
    field_simp
    ring

theorem hasDerivAt_deriv_zetaAtkinsonPhase (T b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv (zetaAtkinsonPhase T b))
      (-T / x ^ 2 - Real.pi * b / (Real.sqrt x) ^ 3) x := by
  apply (hasDerivAt_zetaAtkinsonPhaseDerivative T b hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact (hasDerivAt_zetaAtkinsonPhase T b hy).deriv

end MathCollab.Density.Stronger.Atkinson
