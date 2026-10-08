module
-- Reversible module-visibility port of the audited development.
/-
Native modulus-one adaptation of selected McColm divisor Voronoi residues,
source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright (c) 2026 S. McColm. See repository-root third_party/twelfth/LICENSE-MIT-0.
Mathlib ZetaAsymp and existing rectangle sources retain Apache-2.0 attribution.
No periodic Estermann or upstream project is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiContourBounds
public import MathCollab.Density.Stronger.Atkinson.OrdinaryDivisorMellin

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour MathCollab.Density.Stronger.PointMean
open MathCollab.Density.Stronger.Fourth
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

private theorem voronoi_tendsto_rectangleIntegral'_vertical_sub
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

private theorem voronoi_verticalIntegral'_sub_eq_of_eventual_rectangle
    {f : ℂ → ℂ} {a b : ℝ} {A : ℂ}
    (hBottom : Tendsto (fun R : ℝ => HIntegral' f a b (-R)) atTop (nhds 0))
    (hTop : Tendsto (fun R : ℝ => HIntegral' f a b R) atTop (nhds 0))
    (hIntA : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * I)))
    (hIntB : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * I)))
    (hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) = A) :
    VerticalIntegral' f b - VerticalIntegral' f a = A := by
  have hLimit := voronoi_tendsto_rectangleIntegral'_vertical_sub
    hBottom hTop hIntA hIntB
  have hConst : Tendsto (fun _R : ℝ => A) atTop (nhds A) := tendsto_const_nhds
  have hLimitA := hConst.congr' (hFinite.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hLimit hLimitA


/-- Actual q=1 contour shift, with both vertical integrals and both edges proved. -/
theorem DFIVoronoiTestFunction.ordinaryDivisor_vertical_shift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (3/2) -
      VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (-1/2) =
        ordinaryDivisorVoronoiMain g := by
  obtain ⟨htop,hbottom⟩ := hg.ordinaryDivisor_horizontal_limits
  apply voronoi_verticalIntegral'_sub_eq_of_eventual_rectangle hbottom htop
    (hg.integrable_ordinaryDivisorMellin_vertical (by norm_num) (by norm_num) (by norm_num))
    (hg.integrable_ordinaryDivisorMellin_vertical (by norm_num) (by norm_num) (by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  apply hg.ordinaryDivisor_finiteRectangle
  · norm_num
  · simpa using (show -R ≤ R by linarith)
  · rw [rectangle_mem_nhds_iff]
    norm_num only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, zero_mul, sub_zero, zero_sub,
      add_zero, zero_add, mul_one, one_re, one_im]
    rw [Set.uIoo_of_lt (by norm_num : -(1/2 : ℝ) < 3/2),
      Set.uIoo_of_lt (by linarith : -R < R)]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by simpa using neg_lt_zero.mpr hR, by simpa using hR⟩⟩

/-- Exact native ordinary-divisor Mellin-Barnes formula before the functional equation. -/
theorem DFIVoronoiTestFunction.ordinaryDivisorSum_eq_main_add_left
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n * g n) = ordinaryDivisorVoronoiMain g +
      VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (-1/2) := by
  have hr : (∑' n : ℕ, divisorWeight n * g n) =
      VerticalIntegral' (ordinaryDivisorMellinIntegrand g) (3/2) := by
    rw [verticalIntegral'_eq_realIntegral]
    exact hg.ordinaryDivisorSum_eq_zetaSquareMellinIntegral (by norm_num)
  rw [hr]
  linear_combination hg.ordinaryDivisor_vertical_shift

/-- Exact native FE split, retaining both original Mellin multipliers. -/
theorem DFIVoronoiTestFunction.ordinaryDivisorSum_eq_main_add_reflected
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n * g n) = ordinaryDivisorVoronoiMain g +
      VerticalIntegral' (fun z : ℂ =>
        (dfiVoronoiMinusMultiplier 1 z + dfiVoronoiPlusMultiplier 1 z) *
          riemannZeta (1-z)^2 * mellin g z) (-1/2) := by
  rw [hg.ordinaryDivisorSum_eq_main_add_left]
  congr 1
  rw [verticalIntegral'_eq_realIntegral, verticalIntegral'_eq_realIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  unfold ordinaryDivisorMellinIntegrand
  rw [riemannZeta_sq_eq_voronoiMultipliers (by norm_num)
    (by intro h; have := congrArg Complex.re h; norm_num at this)]

end MathCollab.Density.Stronger.Atkinson
