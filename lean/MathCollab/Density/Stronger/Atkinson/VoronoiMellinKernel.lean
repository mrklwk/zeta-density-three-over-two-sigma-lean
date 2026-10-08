module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiInverseWeights
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Real.Pi.Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology
open Classical
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- The logarithmic-coordinate Mellin kernel attached to a DFI test
function on the vertical line `Re s = σ`. -/
noncomputable def dfiVoronoiMellinKernel
    (σ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-σ * u) : ℂ) * g (Real.exp (-u))

theorem DFIVoronoiTestFunction.contDiff_mellinKernel
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    ContDiff ℝ ∞ (dfiVoronoiMellinKernel σ g) := by
  have hWeight : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp (-σ * u) : ℂ)) := by
    have hInner : ContDiff ℝ ∞ (fun u : ℝ => -σ * u) :=
      contDiff_const.mul contDiff_id
    exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp hInner)
  have hArg : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) := by
    fun_prop
  exact hWeight.mul (hg.smooth.comp hArg)

theorem DFIVoronoiTestFunction.hasCompactSupport_mellinKernel
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    HasCompactSupport (dfiVoronoiMellinKernel σ g) := by
  have hUpperPos : 0 < hg.upper := hg.lower_pos.trans_le hg.lower_le_upper
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log hg.upper) (-Real.log hg.lower)))
  intro u hu
  have hgZero : g (Real.exp (-u)) = 0 := by
    by_contra hne
    have hs := hg.support_subset hne
    apply hu
    rw [Set.mem_Icc]
    constructor
    · have hlog : -u ≤ Real.log hg.upper := by
        apply (Real.exp_le_exp).mp
        rw [Real.exp_log hUpperPos]
        exact hs.2
      linarith
    · have hlog : Real.log hg.lower ≤ -u := by
        apply (Real.exp_le_exp).mp
        rw [Real.exp_log hg.lower_pos]
        exact hs.1
      linarith
  simp [dfiVoronoiMellinKernel, hgZero]

/-- The DFI logarithmic Mellin kernel as a Schwartz function. -/
noncomputable def dfiVoronoiMellinKernelSchwartz
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) : 𝓢(ℝ, ℂ) :=
  (hg.hasCompactSupport_mellinKernel σ).toSchwartzMap
    (hg.contDiff_mellinKernel σ)

@[simp]
theorem DFIVoronoiTestFunction.mellinKernelSchwartz_apply
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ u : ℝ) :
    dfiVoronoiMellinKernelSchwartz hg σ u =
      dfiVoronoiMellinKernel σ g u := rfl

theorem DFIVoronoiTestFunction.mellin_eq_fourier_mellinKernel
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ u : ℝ) :
    mellin g ((σ : ℂ) + (u : ℂ) * I) =
      𝓕 (dfiVoronoiMellinKernelSchwartz hg σ)
        (u / (2 * Real.pi)) := by
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, zero_add, mul_one, neg_mul]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (u / (2 * Real.pi)))
  funext v
  simp [dfiVoronoiMellinKernel]

/-- A compactly supported smooth DFI test function has an integrable Mellin
transform on every complete vertical line.  This is the exact analytic
hypothesis needed by Mathlib's Mellin inversion theorem. -/
theorem DFIVoronoiTestFunction.verticalIntegrable_mellin
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    VerticalIntegrable (mellin g) σ := by
  rw [VerticalIntegrable]
  let F : 𝓢(ℝ, ℂ) := 𝓕 (dfiVoronoiMellinKernelSchwartz hg σ)
  have hFourier : Integrable (F : ℝ → ℂ) := F.integrable
  have hScaled : Integrable
      (fun u : ℝ =>
        𝓕 (dfiVoronoiMellinKernelSchwartz hg σ) (u / (2 * Real.pi))) := by
    simpa [F, div_eq_mul_inv] using
      hFourier.comp_mul_right' (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  apply hScaled.congr
  filter_upwards with u
  exact (hg.mellin_eq_fourier_mellinKernel σ u).symm

/-- Quadratic polynomial growth is integrable against the Mellin transform
of a DFI test function on every vertical line. -/
theorem DFIVoronoiTestFunction.integrable_sqWeight_norm_mellin
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    Integrable (fun u : ℝ =>
      (1 + |u|) ^ 2 * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (dfiVoronoiMellinKernelSchwartz hg σ)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hcOne : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  have h0 : Integrable (fun ξ : ℝ => ‖F ξ‖) := F.integrable.norm
  have h1 : Integrable (fun ξ : ℝ => |ξ| * ‖F ξ‖) := by
    simpa [Real.norm_eq_abs] using F.integrable_pow_mul volume 1
  have h2 : Integrable (fun ξ : ℝ => |ξ| ^ 2 * ‖F ξ‖) := by
    simpa [Real.norm_eq_abs] using F.integrable_pow_mul volume 2
  have hPoly : Integrable (fun ξ : ℝ => (1 + |ξ|) ^ 2 * ‖F ξ‖) := by
    have hSum := h0.add ((h1.const_mul 2).add h2)
    convert hSum using 1
    funext ξ
    simp only [Pi.add_apply]
    ring
  have hScaled : Integrable (fun u : ℝ =>
      (1 + |u / c|) ^ 2 * ‖F (u / c)‖) := by
    simpa [div_eq_mul_inv] using
      hPoly.comp_mul_right' (show c⁻¹ ≠ 0 by positivity)
  have hDom : Integrable (fun u : ℝ =>
      c ^ 2 * ((1 + |u / c|) ^ 2 * ‖F (u / c)‖)) :=
    hScaled.const_mul (c ^ 2)
  have hTargetMeas : AEStronglyMeasurable (fun u : ℝ =>
      (1 + |u|) ^ 2 * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by
    have hCont : Continuous (fun u : ℝ =>
        (1 + |u|) ^ 2 * ‖F (u / c)‖) := by
      fun_prop
    apply hCont.aestronglyMeasurable.congr
    filter_upwards with u
    rw [hg.mellin_eq_fourier_mellinKernel σ u]
  apply hDom.mono' hTargetMeas
  filter_upwards with u
  have hAbsDiv : |u / c| = |u| / c := by
    rw [abs_div, abs_of_pos hc]
  have hLinear : 1 + |u| ≤ c * (1 + |u / c|) := by
    rw [hAbsDiv]
    field_simp
    simpa [add_comm] using add_le_add_right hcOne |u|
  have hSq : (1 + |u|) ^ 2 ≤ c ^ 2 * (1 + |u / c|) ^ 2 := by
    simpa [mul_pow] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) hLinear 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hg.mellin_eq_fourier_mellinKernel σ u]
  simpa [F, c, mul_assoc] using
    mul_le_mul_of_nonneg_right hSq (norm_nonneg (F (u / c)))


end MathCollab.Density.Stronger.Atkinson
