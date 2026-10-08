module
-- Reversible module-visibility port of the audited development.
/-
Native modulus-one adaptation of selected McColm divisor Voronoi residues,
source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright (c) 2026 S. McColm. See repository-root third_party/twelfth/LICENSE-MIT-0.
Mathlib ZetaAsymp and existing rectangle sources retain Apache-2.0 attribution.
No periodic Estermann or upstream project is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMellinDecay
public import MathCollab.Density.Stronger.PointMean.DoublePole
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def ordinaryDivisorMellinIntegrand (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  riemannZeta s ^ 2 * mellin g s

def ordinaryDivisorMellinNumerator (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  riemannZeta₁ s ^ 2 * mellin g s

def ordinaryDivisorVoronoiMain (g : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0, ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * g x

theorem ordinaryDivisorMellinIntegrand_eq_poleCleared (g : ℝ → ℂ) {s : ℂ}
    (hs : s ≠ 1) : ordinaryDivisorMellinIntegrand g s =
      ordinaryDivisorMellinNumerator g s / (s - 1) ^ 2 := by
  unfold ordinaryDivisorMellinIntegrand ordinaryDivisorMellinNumerator
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp [sub_ne_zero.mpr hs]

theorem DFIVoronoiTestFunction.differentiable_ordinaryDivisorMellinNumerator
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    Differentiable ℂ (ordinaryDivisorMellinNumerator g) :=
  (differentiable_riemannZeta₁.pow 2).mul hg.differentiable_mellin

theorem ordinaryDivisorMellinNumerator_one (g : ℝ → ℂ) :
    ordinaryDivisorMellinNumerator g 1 = mellin g 1 := by
  simp [ordinaryDivisorMellinNumerator]

theorem DFIVoronoiTestFunction.deriv_ordinaryDivisorMellinNumerator_one
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    deriv (ordinaryDivisorMellinNumerator g) 1 =
      deriv (mellin g) 1 + 2 * (Real.eulerMascheroniConstant : ℂ) * mellin g 1 := by
  have hz : HasDerivAt riemannZeta₁ (Real.eulerMascheroniConstant : ℂ) 1 := by
    simpa using (differentiable_riemannZeta₁ 1).hasDerivAt
  have hp := (hz.pow 2).mul (hg.differentiable_mellin 1).hasDerivAt
  change deriv (riemannZeta₁ ^ 2 * mellin g) 1 = _
  rw [hp.deriv]
  simp only [Nat.cast_ofNat, Pi.pow_apply, riemannZeta₁_one, one_pow, mul_one, one_mul]
  ring

theorem DFIVoronoiTestFunction.ordinaryDivisor_laurent_mainTerm
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    deriv (ordinaryDivisorMellinNumerator g) 1 = ordinaryDivisorVoronoiMain g := by
  rw [hg.deriv_ordinaryDivisorMellinNumerator_one, hg.mellin_hasDerivAt_one.deriv,
    mellin_log_smul_apply_one, mellin_apply_one]
  have hlog : IntegrableOn (fun x : ℝ => (Real.log x : ℂ) * g x) (Ioi 0) := by
    have hc := (mellin_hasDerivAt_of_isBigO_rpow (s := (1 : ℂ)) (a := (2 : ℝ))
      (b := (0 : ℝ))
      (hg.continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
      (hg.isBigO_atTop (2 : ℝ)) (by norm_num)
      (hg.isBigO_atZero (0 : ℝ)) (by norm_num)).1
    simpa [MellinConvergent, smul_eq_mul] using hc
  have hgInt : IntegrableOn g (Ioi 0) :=
    (hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport).integrableOn
  unfold ordinaryDivisorVoronoiMain
  rw [← integral_const_mul, ← integral_add hlog (hgInt.const_mul (2 * (Real.eulerMascheroniConstant : ℂ)))]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem DFIVoronoiTestFunction.ordinaryDivisor_finiteRectangle
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {z w : ℂ}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 (1 : ℂ)) :
    RectangleIntegral' (ordinaryDivisorMellinIntegrand g) z w =
      ordinaryDivisorVoronoiMain g := by
  have hEq : EqOn (ordinaryDivisorMellinIntegrand g)
      (fun s => ordinaryDivisorMellinNumerator g s / (s - 1)^2) (RectangleBorder z w) := by
    intro s hs
    apply ordinaryDivisorMellinIntegrand_eq_poleCleared
    intro h
    subst s
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds hp hs
  rw [RectangleIntegral'_congr hEq]
  exact (PointMean.rectangleIntegral'_div_sq_eq_deriv hzre hzim hp
    hg.differentiable_ordinaryDivisorMellinNumerator.differentiableOn).trans
      hg.ordinaryDivisor_laurent_mainTerm

end MathCollab.Density.Stronger.Atkinson
