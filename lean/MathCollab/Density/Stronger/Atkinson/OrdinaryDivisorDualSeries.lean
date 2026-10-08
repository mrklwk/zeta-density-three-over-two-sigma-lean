module
-- Reversible module-visibility port of the audited development.
/-
New native modulus-one absolute dual-series exchange. Exact multiplier
conventions originate in S. McColm's DFIVoronoiDual.lean, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1 (MIT-0).
The q=1 exchange proof below is derived directly from the actual divisor
Dirichlet series and Mathlib integral exchange. Apache attribution retained.
-/
public import MathCollab.Density.Stronger.Atkinson.OrdinaryDivisorContourShift
public import MathCollab.Density.Stronger.Fourth.SquareDivisorSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- One complete ordinary-divisor summand on the canonical reflected line. -/
def ordinaryDivisorDualTerm (g : ℝ → ℂ) (K : ℂ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  divisorDirichletTerm (1 - ((-1/2 : ℂ) + (u : ℂ)*I)) n *
    (K ((-1/2 : ℂ) + (u : ℂ)*I) * mellin g ((-1/2 : ℂ) + (u : ℂ)*I))

theorem norm_divisorDirichletTerm_reflected (n : ℕ) (u : ℝ) :
    ‖divisorDirichletTerm (1 - ((-1/2 : ℂ) + (u : ℂ)*I)) n‖ =
      ‖divisorDirichletTerm (3/2) n‖ := by
  simp only [divisorDirichletTerm, LSeries.norm_term_eq]
  norm_num

theorem continuous_divisorDirichletTerm_reflected (n : ℕ) :
    Continuous (fun u : ℝ => divisorDirichletTerm (1 - ((-1/2 : ℂ) + (u : ℂ)*I)) n) := by
  have h := (continuous_divisorDirichletTerm_vertical 0 1 n).comp continuous_neg
  convert h using 1
  funext u
  congr 1
  unfold afeCriticalPoint
  push_cast
  ring

/-- Explicit helper for an integrable dual multiplier times the actual Mellin transform. -/
theorem integrable_ordinaryDivisorDualTerm {g : ℝ → ℂ} {K : ℂ → ℂ}
    (hK : Integrable (fun u : ℝ => K ((-1/2 : ℂ)+(u : ℂ)*I) *
      mellin g ((-1/2 : ℂ)+(u : ℂ)*I))) (n : ℕ) :
    Integrable (ordinaryDivisorDualTerm g K n) := by
  apply hK.bdd_mul (c := ‖divisorDirichletTerm (3/2) n‖)
    (continuous_divisorDirichletTerm_reflected n).aestronglyMeasurable
  exact Eventually.of_forall fun u => (norm_divisorDirichletTerm_reflected n u).le

theorem integral_norm_ordinaryDivisorDualTerm (g : ℝ → ℂ) (K : ℂ → ℂ) (n : ℕ) :
    (∫ u : ℝ, ‖ordinaryDivisorDualTerm g K n u‖) =
      ‖divisorDirichletTerm (3/2) n‖ *
        ∫ u : ℝ, ‖K ((-1/2 : ℂ)+(u : ℂ)*I) * mellin g ((-1/2 : ℂ)+(u : ℂ)*I)‖ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [ordinaryDivisorDualTerm, norm_mul, norm_divisorDirichletTerm_reflected]

theorem summable_integral_norm_ordinaryDivisorDualTerm (g : ℝ → ℂ) (K : ℂ → ℂ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖ordinaryDivisorDualTerm g K n u‖) := by
  simp_rw [integral_norm_ordinaryDivisorDualTerm]
  exact (summable_divisorDirichletTerm (s := (3/2 : ℂ)) (by norm_num)).norm.mul_right _

theorem tsum_ordinaryDivisorDualTerm (g : ℝ → ℂ) (K : ℂ → ℂ) (u : ℝ) :
    (∑' n : ℕ, ordinaryDivisorDualTerm g K n u) =
      riemannZeta (1-((-1/2 : ℂ)+(u : ℂ)*I))^2 *
        K ((-1/2 : ℂ)+(u : ℂ)*I) * mellin g ((-1/2 : ℂ)+(u : ℂ)*I) := by
  unfold ordinaryDivisorDualTerm
  rw [tsum_mul_right, tsum_divisorDirichletTerm,
    ← riemannZeta_sq_eq_divisorLSeries (by norm_num)]
  ring

/-- Full reflected integrand is integrable, not merely each individual term. -/
theorem integrable_zetaSquare_dualMultiplier {g : ℝ → ℂ} {K : ℂ → ℂ}
    (hK : Integrable (fun u : ℝ => K ((-1/2 : ℂ)+(u : ℂ)*I) *
      mellin g ((-1/2 : ℂ)+(u : ℂ)*I))) :
    Integrable (fun u : ℝ => riemannZeta (1-((-1/2 : ℂ)+(u : ℂ)*I))^2 *
      K ((-1/2 : ℂ)+(u : ℂ)*I) * mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) := by
  have hcont : Continuous (fun u : ℝ => riemannZeta (1-((-1/2 : ℂ)+(u : ℂ)*I))^2) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hn : 1-((-1/2 : ℂ)+(u : ℂ)*I) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    exact ContinuousAt.comp (f := fun u : ℝ => 1-((-1/2 : ℂ)+(u : ℂ)*I))
      (g := riemannZeta ^ 2) ((differentiableAt_riemannZeta hn).pow 2).continuousAt (by fun_prop)
  have hb (u : ℝ) : ‖riemannZeta (1-((-1/2 : ℂ)+(u : ℂ)*I))^2‖ ≤
      ∑' n : ℕ, ‖divisorDirichletTerm (3/2) n‖ := by
    rw [riemannZeta_sq_eq_divisorLSeries (by norm_num), ← tsum_divisorDirichletTerm]
    apply (norm_tsum_le_tsum_norm (summable_divisorDirichletTerm (by norm_num)).norm).trans
    exact le_of_eq (tsum_congr fun n => norm_divisorDirichletTerm_reflected n u)
  have h := hK.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall hb)
  simpa only [mul_assoc] using h

theorem divisorWeight_mul_dualTransform (g : ℝ → ℂ) (K : ℂ → ℂ) (n : ℕ) :
    divisorWeight n * PointMean.VerticalIntegral'
      (fun z : ℂ => (n : ℂ)^(-(1-z)) * K z * mellin g z) (-1/2) =
      (1/(2*Real.pi) : ℂ) * ∫ u : ℝ, ordinaryDivisorDualTerm g K n u := by
  rw [verticalIntegral'_eq_realIntegral]
  norm_num only [ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]
  have h (u : ℝ) : ordinaryDivisorDualTerm g K n u = divisorWeight n *
      ((n : ℂ)^(-(1-((-1/2 : ℂ)+(u : ℂ)*I))) *
        K ((-1/2 : ℂ)+(u : ℂ)*I) * mellin g ((-1/2 : ℂ)+(u : ℂ)*I)) := by
    rw [ordinaryDivisorDualTerm, divisorDirichletTerm_eq_divisorWeight_mul_cpow]
    ring
  simp_rw [h]
  rw [integral_const_mul]
  simp only [neg_div]
  ring

theorem summable_divisorWeight_dualTransform {g : ℝ → ℂ} {K : ℂ → ℂ}
    (hK : Integrable (fun u : ℝ => K ((-1/2 : ℂ)+(u : ℂ)*I) *
      mellin g ((-1/2 : ℂ)+(u : ℂ)*I))) :
    Summable (fun n : ℕ => divisorWeight n * PointMean.VerticalIntegral'
      (fun z : ℂ => (n : ℂ)^(-(1-z)) * K z * mellin g z) (-1/2)) := by
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_ordinaryDivisorDualTerm hK) (summable_integral_norm_ordinaryDivisorDualTerm g K)
  simpa only [divisorWeight_mul_dualTransform] using h.summable.mul_left (1/(2*Real.pi) : ℂ)

theorem tsum_divisorWeight_dualTransform {g : ℝ → ℂ} {K : ℂ → ℂ}
    (hK : Integrable (fun u : ℝ => K ((-1/2 : ℂ)+(u : ℂ)*I) *
      mellin g ((-1/2 : ℂ)+(u : ℂ)*I))) :
    (∑' n : ℕ, divisorWeight n * PointMean.VerticalIntegral'
      (fun z : ℂ => (n : ℂ)^(-(1-z)) * K z * mellin g z) (-1/2)) =
      PointMean.VerticalIntegral' (fun z : ℂ => riemannZeta (1-z)^2 * K z * mellin g z) (-1/2) := by
  simp_rw [divisorWeight_mul_dualTransform]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
    (integrable_ordinaryDivisorDualTerm hK) (summable_integral_norm_ordinaryDivisorDualTerm g K)]
  rw [verticalIntegral'_eq_realIntegral]
  simp_rw [tsum_ordinaryDivisorDualTerm]
  norm_num only [ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]

end MathCollab.Density.Stronger.Atkinson
