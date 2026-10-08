module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightSmooth
public import MathCollab.Density.Stronger.Fourth.GammaShiftLog
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeRescaled

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaMainMellinProfile (u : ℝ) : ℂ :=
  zetaDivisorWeight ((Real.log u + Real.log (2 * Real.pi) : ℝ) +
    (Real.pi / 2 : ℝ) * I)

theorem contDiffAt_zetaMainMellinProfile {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ 1 zetaMainMellinProfile u := by
  have hl : ContDiffAt ℝ 1 Real.log u := Real.contDiffAt_log.mpr hu.ne'
  have hc : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hw : ContDiff ℝ 1 zetaDivisorWeight := contDiff_zetaDivisorWeight.of_le (by simp)
  unfold zetaMainMellinProfile
  fun_prop

theorem zetaDivisorWeight_source_eq_profile {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    zetaDivisorWeight ((Real.log x : ℂ) - zetaGammaLeadingLog T) =
      zetaMainMellinProfile (x / T) := by
  unfold zetaMainMellinProfile zetaGammaLeadingLog
  rw [Real.log_div hx.ne' hT.ne', Real.log_div hT.ne' (by positivity : 2 * Real.pi ≠ 0)]
  congr 1
  push_cast
  ring

theorem exists_intervalC1Bound_zetaMainMellinProfile :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      IntervalC1Bound (fun x => zetaMainMellinProfile (x / T)) (T / 16) T C :=
  exists_intervalC1Bound_rescaled (fun _ hu => contDiffAt_zetaMainMellinProfile hu)

def atkinsonPowerProfile (α u : ℝ) : ℂ :=
  ((u ^ (-α) : ℝ) : ℂ) * zetaMainMellinProfile u

theorem contDiffAt_atkinsonPowerProfile (α : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ 1 (atkinsonPowerProfile α) u := by
  have hm := contDiffAt_zetaMainMellinProfile hu
  have hp : ContDiffAt ℝ 1 (fun v : ℝ => v ^ (-α)) u := by
    fun_prop (disch := exact hu.ne')
  unfold atkinsonPowerProfile
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u hp).mul hm

theorem exists_intervalC2Bound_atkinsonPowerRootProfile (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      IntervalC2Bound (fun u => atkinsonPowerProfile α (u ^ 2)) (1 / 4) 1 C 1 := by
  apply exists_intervalC2Bound_fixed
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hw : ContDiff ℝ 2 zetaDivisorWeight :=
    contDiff_zetaDivisorWeight.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))
  have hcast : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold atkinsonPowerProfile zetaMainMellinProfile
  fun_prop (disch := positivity)

end MathCollab.Density.Stronger.Atkinson
