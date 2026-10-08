module
-- Reversible module-visibility port of the audited development.
/-
New native q=1 Voronoi proof, with both complete dual series absolutely convergent.
The exact statement follows S. McColm, ZetaDivisorVoronoi.lean, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1 (MIT-0).
This proof uses the genuine compact-test contour shift and actual zeta functional
equation; no general Estermann summation formula is imported or assumed.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.OrdinaryDivisorDualSeries
public import MathCollab.Density.Stronger.Atkinson.VoronoiMultiplierBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- Explicit domination helper. Its continuity and growth premises are discharged
for both literal Voronoi multipliers below. -/
theorem DFIVoronoiTestFunction.integrable_dualMultiplier_of_quadratic_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {K : ℂ → ℂ} {C : ℝ}
    (hcont : Continuous (fun u : ℝ => K ((-1/2 : ℂ)+(u : ℂ)*I)))
    (hb : ∀ u : ℝ, ‖K ((-1/2 : ℂ)+(u : ℂ)*I)‖ ≤ C*(1+|u|)^2) :
    Integrable (fun u : ℝ => K ((-1/2 : ℂ)+(u : ℂ)*I)*
      mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) := by
  have hcontM : Continuous (fun u : ℝ => mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) :=
    hg.differentiable_mellin.continuous.comp (by fun_prop)
  have hInt := (hg.integrable_sqWeight_norm_mellin (-1/2)).const_mul C
  norm_num only [ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat] at hInt
  apply hInt.mono' (hcont.mul hcontM).aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  simp only [Pi.mul_apply, norm_mul]
  calc
    _ ≤ (C*(1+|u|)^2)*‖mellin g ((-1/2 : ℂ)+(u : ℂ)*I)‖ :=
      mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)
    _ = _ := by simp only [neg_div]; ring

theorem DFIVoronoiTestFunction.integrable_voronoiMinusMultiplier
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    Integrable (fun u : ℝ => dfiVoronoiMinusMultiplier 1 ((-1/2 : ℂ)+(u : ℂ)*I)*
      mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) := by
  apply hg.integrable_dualMultiplier_of_quadratic_bound (C := 10368)
  · apply continuous_iff_continuousAt.mpr
    intro u
    exact (differentiableAt_dfiVoronoiMinusMultiplier_of_re_lt_one 1 (by norm_num)).continuousAt.comp
      (f := fun v : ℝ => (-1/2 : ℂ)+(v : ℂ)*I) (by fun_prop)
  · intro u
    simpa using norm_dfiVoronoiMinusMultiplier_strip_le 1
      (z := (-1/2 : ℂ)+(u : ℂ)*I) (by norm_num) (by norm_num)

theorem DFIVoronoiTestFunction.integrable_voronoiPlusMultiplier
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    Integrable (fun u : ℝ => dfiVoronoiPlusMultiplier 1 ((-1/2 : ℂ)+(u : ℂ)*I)*
      mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) := by
  apply hg.integrable_dualMultiplier_of_quadratic_bound (C := 10368)
  · apply continuous_iff_continuousAt.mpr
    intro u
    exact (differentiableAt_dfiVoronoiPlusMultiplier_of_re_lt_one 1 (by norm_num)).continuousAt.comp
      (f := fun v : ℝ => (-1/2 : ℂ)+(v : ℂ)*I) (by fun_prop)
  · intro u
    simpa using norm_dfiVoronoiPlusMultiplier_strip_le 1
      (z := (-1/2 : ℂ)+(u : ℂ)*I) (by norm_num) (by norm_num)

/-- Absolute convergence of the complete native minus series, including n=0. -/
theorem DFIVoronoiTestFunction.summable_divisorWeight_voronoiMinus
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    Summable (fun n : ℕ => divisorWeight n * dfiVoronoiMinusTransform 1 (mellin g) n) := by
  simpa only [dfiVoronoiMinusTransform, neg_div] using
    summable_divisorWeight_dualTransform hg.integrable_voronoiMinusMultiplier

/-- Absolute convergence of the complete native plus series, including n=0. -/
theorem DFIVoronoiTestFunction.summable_divisorWeight_voronoiPlus
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    Summable (fun n : ℕ => divisorWeight n * dfiVoronoiPlusTransform 1 (mellin g) n) := by
  simpa only [dfiVoronoiPlusTransform, neg_div] using
    summable_divisorWeight_dualTransform hg.integrable_voronoiPlusMultiplier

/-- Genuine q=1 Voronoi identity, with the exact logarithmic main term and
both original Mellin transforms; all contour and exchange conditions proved. -/
theorem ordinaryDivisorVoronoi_native {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n*g n) = ordinaryDivisorVoronoiMain g +
      (∑' n : ℕ, divisorWeight n*dfiVoronoiMinusTransform 1 (mellin g) n) +
      (∑' n : ℕ, divisorWeight n*dfiVoronoiPlusTransform 1 (mellin g) n) := by
  rw [hg.ordinaryDivisorSum_eq_main_add_reflected]
  unfold dfiVoronoiMinusTransform dfiVoronoiPlusTransform
  simp only [← neg_div]
  rw [tsum_divisorWeight_dualTransform hg.integrable_voronoiMinusMultiplier,
    tsum_divisorWeight_dualTransform hg.integrable_voronoiPlusMultiplier]
  simp only [verticalIntegral'_eq_realIntegral]
  norm_num only [ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]
  simp only [← neg_div]
  have hfun : (fun u : ℝ =>
      (dfiVoronoiMinusMultiplier 1 ((-1/2 : ℂ)+(u : ℂ)*I) +
        dfiVoronoiPlusMultiplier 1 ((-1/2 : ℂ)+(u : ℂ)*I))*
      riemannZeta (1-((-1/2 : ℂ)+(u : ℂ)*I))^2*mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) =
    (fun u : ℝ =>
      riemannZeta (1-((-1/2 : ℂ)+(u : ℂ)*I))^2*
        dfiVoronoiMinusMultiplier 1 ((-1/2 : ℂ)+(u : ℂ)*I)*mellin g ((-1/2 : ℂ)+(u : ℂ)*I) +
      riemannZeta (1-((-1/2 : ℂ)+(u : ℂ)*I))^2*
        dfiVoronoiPlusMultiplier 1 ((-1/2 : ℂ)+(u : ℂ)*I)*mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) := by
    funext u; ring
  rw [hfun, integral_add
    (integrable_zetaSquare_dualMultiplier hg.integrable_voronoiMinusMultiplier)
    (integrable_zetaSquare_dualMultiplier hg.integrable_voronoiPlusMultiplier)]
  ring

end MathCollab.Density.Stronger.Atkinson
