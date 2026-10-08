module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightSmooth
public import MathCollab.Density.Stronger.Atkinson.ShortDivisorGeometry

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


theorem contDiff_zetaGaussianQuadraticIntegral (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    ContDiff ℝ ∞ (zetaGaussianQuadraticIntegral T G) := by
  have he : zetaGaussianQuadraticIntegral T G = fun v : ℝ =>
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-(v : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G)) := by
    funext v
    exact zetaGaussianQuadraticIntegral_eq T v hG
  rw [he]
  have hcast : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

theorem contDiffAt_ofReal_cpow_positive (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) ^ s) x := by
  have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx.ne'
  have hcastlog : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog
  have hexp : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * s)) x := by
    fun_prop
  apply hexp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hy), ← Complex.ofReal_log hy.le]

theorem contDiffAt_zetaShortDivisorTestFunction (T : ℝ) {G x : ℝ}
    (hG : G ≠ 0) (hx : 0 < x) :
    ContDiffAt ℝ ∞ (zetaShortDivisorTestFunction T G) x := by
  have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx.ne'
  have hpow := contDiffAt_ofReal_cpow_positive ((-1 / 2 : ℂ) + (T : ℂ) * I) hx
  have hcastlog : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog
  have hweight : ContDiffAt ℝ ∞
      (fun y : ℝ => zetaDivisorWeight ((Real.log y : ℂ) - zetaGammaLeadingLog T)) x :=
    contDiff_zetaDivisorWeight.contDiffAt.comp x (hcastlog.sub contDiffAt_const)
  have hquad := contDiff_zetaGaussianQuadraticIntegral T hG
  unfold zetaShortDivisorTestFunction
  fun_prop

theorem contDiffOn_zetaShortDivisorTestFunction (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    ContDiffOn ℝ ∞ (zetaShortDivisorTestFunction T G) (Ioi 0) :=
  fun _ hx => (contDiffAt_zetaShortDivisorTestFunction T hG hx).contDiffWithinAt

end MathCollab.Density.Stronger.Atkinson
