module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.DampedCutoff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.CauchyIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Set MeasureTheory Filter Asymptotics
open scoped ContDiff Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- A positive compactly supported cutoff vanishes at infinity faster than
every fixed real power. -/
theorem positive_compact_cutoff_isBigO_atTop {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (c : ℝ) :
    f =O[atTop] (fun x : ℝ => x^c) := by
  apply IsBigO.of_bound 0
  filter_upwards [eventually_gt_atTop b] with x hx
  have hz : f x = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (not_le.mpr hx) (hs hh).2)
  simp [hz]

/-- The same cutoff vanishes on a right neighbourhood of zero. -/
theorem positive_compact_cutoff_isBigO_zero {f : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hs : tsupport f ⊆ Icc a b) (c : ℝ) :
    f =O[𝓝[>] 0] (fun x : ℝ => x^c) := by
  apply IsBigO.of_bound 0
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ha)] with x hx
  have hz : f x = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (not_le.mpr hx) (hs hh).1)
  simp [hz]

/-- The actual Mellin transform is complex differentiable everywhere; its
derivative is the Mellin transform after multiplication by the real logarithm. -/
theorem positive_compact_cutoff_mellin_hasDerivAt {f : ℝ → ℂ} {a b : ℝ}
    (hf : Continuous f) (ha : 0 < a) (hs : tsupport f ⊆ Icc a b) (s : ℂ) :
    MellinConvergent (fun y => Real.log y • f y) s ∧
      HasDerivAt (mellin f) (mellin (fun y => Real.log y • f y) s) s := by
  exact mellin_hasDerivAt_of_isBigO_rpow (hf.locallyIntegrable.locallyIntegrableOn _)
    (positive_compact_cutoff_isBigO_atTop hs (-(s.re+1))) (by linarith)
    (positive_compact_cutoff_isBigO_zero ha hs (-(s.re-1))) (by linarith)

theorem positive_compact_cutoff_mellin_differentiable {f : ℝ → ℂ} {a b : ℝ}
    (hf : Continuous f) (ha : 0 < a) (hs : tsupport f ⊆ Icc a b) :
    Differentiable ℂ (mellin f) :=
  fun s => (positive_compact_cutoff_mellin_hasDerivAt hf ha hs s).2.differentiableAt

theorem dampedCutoff_mellin_entire {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hs : tsupport ψ ⊆ Icc a b) (q : ℝ) :
    AnalyticOnNhd ℂ (mellin (fun y => (dampedCutoff ψ q y : ℂ))) univ := by
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  apply positive_compact_cutoff_mellin_differentiable
    (Complex.continuous_ofReal.comp (dampedCutoff_contDiff hψ q).continuous) ha
  exact (tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) rfl _).trans
    ((dampedCutoff_tsupport ψ q).trans hs)

end MathCollab.Density.Stronger
