module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIMellinPairing.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMellinInversion
public import MathCollab.Density.Stronger.Atkinson.VoronoiTransforms
public import Mathlib.Analysis.MellinInversion
public import Mathlib.MeasureTheory.Integral.Prod

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Mellin pairing for DFI test functions

This file proves the Mellin Parseval identity needed to identify the
Mellin--Barnes transforms in DFI Proposition 1 with their literal Bessel
integrals.  The proof uses Mathlib's kernel-checked Mellin inversion and an
explicit Tonelli majorant.
-/

open Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap Topology

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- Absolute Mellin convergence recovers measurability of the underlying
physical function on the positive half-line. -/
theorem MellinConvergent.aestronglyMeasurable_positive
    {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)) := by
  have hf' : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • f x) (Set.Ioi 0) := by
    simpa only [MellinConvergent] using hf
  let w : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s - 1))
  have hwCont : ContinuousOn w (Set.Ioi 0) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    exact Complex.continuousAt_ofReal_cpow_const x (-(s - 1))
      (Or.inr hx.ne')
  have hwMeas : AEStronglyMeasurable w
      (volume.restrict (Set.Ioi 0)) :=
    hwCont.aestronglyMeasurable measurableSet_Ioi
  have hWeighted : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x)
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [MellinConvergent, smul_eq_mul] using
      hf'.aestronglyMeasurable
  apply (hwMeas.mul hWeighted).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  dsimp [w]
  rw [← mul_assoc, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr hx.ne')]
  simp

/-- The real norm majorant encoded by Mellin convergence. -/
theorem MellinConvergent.integrableOn_rpow_mul_norm
    {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * ‖f x‖)
      (Set.Ioi 0) := by
  have hf' : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • f x) (Set.Ioi 0) := by
    simpa only [MellinConvergent] using hf
  have hnorm : IntegrableOn
      (fun x : ℝ => ‖(x : ℂ) ^ (s - 1) • f x‖) (Set.Ioi 0) :=
    hf'.norm
  refine hnorm.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [norm_smul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 2

/-- The Mellin transform of a DFI test function is continuous along every
vertical line. -/
theorem DFIVoronoiTestFunction.continuous_mellin_vertical
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    Continuous (fun u : ℝ =>
      mellin g ((σ : ℂ) + (u : ℂ) * I)) := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (dfiVoronoiMellinKernelSchwartz hg σ)
  have hF : Continuous (F : ℝ → ℂ) := F.continuous
  have hComp : Continuous (fun u : ℝ => F (u / (2 * Real.pi))) := by
    fun_prop
  apply hComp.congr
  intro u
  exact (hg.mellin_eq_fourier_mellinKernel σ u).symm

/-- Mellin Parseval for one compactly supported smooth DFI source and one
physical kernel.  The weighted integrability hypothesis is exactly the
absolute-convergence condition needed to exchange the source integral with
the complete vertical line. -/
theorem verticalIntegral'_mellin_mul_mellin_one_sub
    {g h : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ)
    (hhMeas : AEStronglyMeasurable h
      (volume.restrict (Set.Ioi 0)))
    (hhInt : IntegrableOn
      (fun x : ℝ => x ^ (-σ) * ‖h x‖) (Set.Ioi 0)) :
    PointMean.VerticalIntegral'
        (fun z : ℂ => mellin g z * mellin h (1 - z)) σ =
      ∫ x : ℝ in Set.Ioi 0, g x * h x := by
  let z : ℝ → ℂ := fun u => (σ : ℂ) + (u : ℂ) * I
  let F : ℝ × ℝ → ℂ := fun p =>
    mellin g (z p.1) * ((p.2 : ℂ) ^ (-z p.1) * h p.2)
  have hMellinInt : Integrable (fun u : ℝ => ‖mellin g (z u)‖) := by
    simpa [z, VerticalIntegrable] using (hg.verticalIntegrable_mellin σ).norm
  have hMajor : Integrable (fun p : ℝ × ℝ =>
      ‖mellin g (z p.1)‖ * (p.2 ^ (-σ) * ‖h p.2‖))
      (volume.prod (volume.restrict (Set.Ioi 0))) :=
    hMellinInt.mul_prod hhInt
  let F₀ : ℝ × ℝ → ℂ := fun p =>
    mellin g (z p.1) * (p.2 : ℂ) ^ (-z p.1)
  have hF₀Cont : ContinuousOn F₀ (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
    intro p hp
    have hpPos : 0 < p.2 := hp.2
    have hMellin : ContinuousAt (fun r : ℝ × ℝ => mellin g (z r.1)) p :=
      (hg.continuous_mellin_vertical σ).continuousAt.comp (by fun_prop)
    have hPow : ContinuousAt
        (fun r : ℝ × ℝ => (r.2 : ℂ) ^ (-z r.1)) p := by
      have hBaseExp : ContinuousAt
          (fun r : ℝ × ℝ => ((r.2, -z r.1) : ℝ × ℂ)) p := by
        fun_prop
      exact (Complex.continuousAt_ofReal_cpow p.2 (-z p.1)
        (Or.inr hpPos.ne')).comp_of_eq hBaseExp rfl
    exact hMellin.continuousWithinAt.mul hPow.continuousWithinAt
  have hFMeas : AEStronglyMeasurable F
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    have hF₀Meas : AEStronglyMeasurable F₀
        ((volume.prod volume).restrict (Set.univ ×ˢ Set.Ioi (0 : ℝ))) :=
      hF₀Cont.aestronglyMeasurable
        (MeasurableSet.univ.prod measurableSet_Ioi)
    have hMeasure : (volume : Measure ℝ).prod
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
      calc
        (volume : Measure ℝ).prod
              ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) =
            ((volume : Measure ℝ).restrict Set.univ).prod
              ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
                rw [Measure.restrict_univ]
        _ = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
              (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
          Measure.prod_restrict Set.univ (Set.Ioi (0 : ℝ))
    have hF₀Meas' : AEStronglyMeasurable F₀
        (volume.prod (volume.restrict (Set.Ioi 0))) := by
      rw [hMeasure]
      exact hF₀Meas
    exact (hF₀Meas'.mul hhMeas.comp_snd).congr
      (Filter.Eventually.of_forall fun p => by
        change (mellin g (z p.1) * (p.2 : ℂ) ^ (-z p.1)) * h p.2 =
          mellin g (z p.1) * ((p.2 : ℂ) ^ (-z p.1) * h p.2)
        ring)
  have hFInt : Integrable F
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    apply hMajor.mono' hFMeas
    have hPoint : ∀ᵐ p ∂(volume.prod volume).restrict
        (Set.univ ×ˢ Set.Ioi (0 : ℝ)),
        ‖F p‖ ≤ ‖mellin g (z p.1)‖ * (p.2 ^ (-σ) * ‖h p.2‖) := by
      filter_upwards [ae_restrict_mem
        (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
      have hpPos : 0 < p.2 := hp.2
      dsimp [F]
      rw [norm_mul, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
      have hre : (-z p.1).re = -σ := by
        simp [z]
      rw [hre]
    rw [← Measure.prod_restrict] at hPoint
    simpa using hPoint
  have hSwap :
      (∫ u : ℝ, ∫ x : ℝ in Set.Ioi 0, F (u, x)) =
        ∫ x : ℝ in Set.Ioi 0, ∫ u : ℝ, F (u, x) := by
    exact integral_integral_swap hFInt
  have hInner (u : ℝ) :
      (∫ x : ℝ in Set.Ioi 0, F (u, x)) =
        mellin g (z u) * mellin h (1 - z u) := by
    dsimp [F]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show 1 - z u - 1 = -z u by ring]
    ring
  have hOuter (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
      (1 / (2 * Real.pi) : ℂ) * (∫ u : ℝ, F (u, x)) =
        g x * h x := by
    have hInv := hg.mellinInversion σ hx
    unfold mellinInv at hInv
    simp only [Complex.real_smul, smul_eq_mul] at hInv
    dsimp [F, z]
    rw [show (∫ u : ℝ,
        mellin g ((σ : ℂ) + (u : ℂ) * I) *
          ((x : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * I)) * h x)) =
        (∫ u : ℝ,
          (x : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * I)) *
            mellin g ((σ : ℂ) + (u : ℂ) * I)) * h x by
      rw [← MeasureTheory.integral_mul_const]
      apply integral_congr_ae
      filter_upwards with u
      ring]
    have hInv' : (1 / (2 * (Real.pi : ℂ))) *
        (∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) *
          mellin g ((σ : ℂ) + (y : ℂ) * I)) = g x := by
      have hScalar : ((1 / (2 * Real.pi) : ℝ) : ℂ) =
          1 / (2 * (Real.pi : ℂ)) := by
        norm_cast
      rw [← hScalar]
      exact hInv
    rw [← mul_assoc, hInv']
  unfold PointMean.VerticalIntegral' PointMean.VerticalIntegral
  simp only [smul_eq_mul]
  have hNorm : (1 / (2 * Real.pi * I) : ℂ) * I =
      (1 / (2 * Real.pi) : ℂ) := by
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hNorm]
  rw [show (∫ u : ℝ,
      mellin g ((σ : ℂ) + (u : ℂ) * I) *
        mellin h (1 - ((σ : ℂ) + (u : ℂ) * I))) =
      ∫ u : ℝ, ∫ x : ℝ in Set.Ioi 0, F (u, x) by
    apply integral_congr_ae
    filter_upwards with u
    exact (hInner u).symm]
  rw [hSwap, ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact hOuter x hx

end MathCollab.Density.Stronger.Atkinson
