module
-- Reversible module-visibility port of the audited development.
/-
Canonical minus contour transport for the literal DFI Bessel multiplier.
Target and selected rectangle-limit proof pattern: Scott McColm,
DFIEquation29.lean and PointMeanMellinShift.lean, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, copyright 2026, MIT-0.
The existing PNT+ rectangle infrastructure retains Apache-2.0 attribution.
The final physical identity has no convergence or contour-identity premise.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMinusConvergence
public import MathCollab.Density.Stronger.Atkinson.BesselTransformBridge

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour MathCollab.Density.Stronger.PointMean
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

private theorem tendsto_rectangleIntegral'_vertical_sub
    {f : ℂ → ℂ} {a b : ℝ}
    (hBottom : Tendsto (fun R : ℝ => HIntegral' f a b (-R)) atTop (nhds 0))
    (hTop : Tendsto (fun R : ℝ => HIntegral' f a b R) atTop (nhds 0))
    (hIntA : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * I)))
    (hIntB : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * I))) :
    Tendsto (fun R : ℝ =>
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I)) atTop
      (nhds (VerticalIntegral' f b - VerticalIntegral' f a)) := by
  let c : ℂ := (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have hRight : Tendsto (fun R : ℝ =>
      c * ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) atTop
      (nhds (c * ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I))) :=
    (intervalIntegral_tendsto_integral hIntB
      tendsto_neg_atTop_atBot tendsto_id).const_mul c
  have hLeft : Tendsto (fun R : ℝ =>
      c * ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) atTop
      (nhds (c * ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I))) :=
    (intervalIntegral_tendsto_integral hIntA
      tendsto_neg_atTop_atBot tendsto_id).const_mul c
  have hEdges := (hBottom.sub hTop).add (hRight.sub hLeft)
  have hExpanded : Tendsto (fun R : ℝ =>
      HIntegral' f a b (-R) - HIntegral' f a b R +
        ((c * ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
          c * ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I))) atTop
      (nhds (c * (∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I)) -
        c * (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)))) := by
    simpa only [zero_sub, neg_zero, zero_add] using hEdges
  have hRectangle : Tendsto (fun R : ℝ =>
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I)) atTop
      (nhds (c * (∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I)) -
        c * (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)))) := by
    refine hExpanded.congr' ?_
    filter_upwards with R
    rw [pintz2023_RectangleIntegral'_eq_edges]
    dsimp only [c]
    ring
  have hVerticalB : VerticalIntegral' f b =
      c * ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I) := by
    unfold VerticalIntegral' VerticalIntegral
    dsimp only [c]
    simp [smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hVerticalA : VerticalIntegral' f a =
      c * ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I) := by
    unfold VerticalIntegral' VerticalIntegral
    dsimp only [c]
    simp [smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  simpa only [hVerticalB, hVerticalA] using hRectangle

private theorem verticalIntegral'_sub_eq_of_eventual_rectangle
    {f : ℂ → ℂ} {a b : ℝ} {A : ℂ}
    (hBottom : Tendsto (fun R : ℝ => HIntegral' f a b (-R)) atTop (nhds 0))
    (hTop : Tendsto (fun R : ℝ => HIntegral' f a b R) atTop (nhds 0))
    (hIntA : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * I)))
    (hIntB : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * I)))
    (hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) = A) :
    VerticalIntegral' f b - VerticalIntegral' f a = A := by
  have hLimit := tendsto_rectangleIntegral'_vertical_sub
    hBottom hTop hIntA hIntB
  have hConst : Tendsto (fun _R : ℝ => A) atTop (nhds A) := tendsto_const_nhds
  have hLimitA := hConst.congr' (hFinite.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hLimit hLimitA

theorem DFIVoronoiTestFunction.minusIntegrand_finite_rectangle (q : ℕ) [NeZero q]
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {n : ℕ} (hn : 0<n)
    (H : ℝ) :
    RectangleIntegral' (dfiVoronoiMinusIntegrand q g n)
      ((-(1/2) : ℂ)-(H:ℂ)*I) ((13/16 : ℂ)+(H:ℂ)*I) = 0 := by
  have hh : HolomorphicOn (dfiVoronoiMinusIntegrand q g n) {z : ℂ | z.re < 1} := by
    intro z hz
    exact (differentiableAt_dfiVoronoiMinusIntegrand q hg hn hz).differentiableWithinAt
  have hr := hh.vanishesOnRectangle (z := (-(1/2) : ℂ)-(H:ℂ)*I)
    (w := (13/16 : ℂ)+(H:ℂ)*I) (by
      intro z hz
      have hzre := hz.1
      change z.re ∈ Set.uIcc _ _ at hzre
      norm_num at hzre
      change z.re < 1
      linarith [hzre.2])
  simp only [RectangleIntegral', hr, smul_zero]

theorem DFIVoronoiTestFunction.minusTransform_eq_thirteenSixteenths
    (q : ℕ) [NeZero q] {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {n : ℕ} (hn : 0<n) :
    dfiVoronoiMinusTransform q (mellin g) n =
      PointMean.VerticalIntegral' (dfiVoronoiMinusIntegrand q g n) (13/16) := by
  obtain ⟨htop,hbottom⟩ := hg.minusIntegrand_horizontal_limits q hn
  have ha := hg.integrable_minusIntegrand_vertical q hn
    (σ := -(1/2 : ℝ)) (by norm_num) (by norm_num)
  have hb := hg.integrable_minusIntegrand_vertical q hn
    (σ := (13/16 : ℝ)) (by norm_num) (by norm_num)
  have h := verticalIntegral'_sub_eq_of_eventual_rectangle hbottom htop ha hb
    (A := 0) (Eventually.of_forall fun H => by
      simpa using hg.minusIntegrand_finite_rectangle q hn H)
  exact (sub_eq_zero.mp h).symm

/-- Canonical Mellin--Barnes minus transform equals the literal Schläfli Y₀
transform. All line integrability and horizontal decay are discharged. -/
theorem dfiVoronoiMinusTransform_mellin_eq_bessel (q n : ℕ) [NeZero q]
    (hn : 0<n) {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    dfiVoronoiMinusTransform q (mellin g) n = dfiVoronoiMinusBesselTransform q g n := by
  rw [hg.minusTransform_eq_thirteenSixteenths q hn]
  exact verticalIntegral_dfiVoronoiMinus_mellin_thirteenSixteenths_eq_bessel q n hn hg

end MathCollab.Density.Stronger.Atkinson
