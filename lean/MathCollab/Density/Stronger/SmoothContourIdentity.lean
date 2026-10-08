module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothContourEstimates

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open MathCollab.Density.Contour
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Exact second contour shift for the actual smooth Mellin kernel. The only
residue is at the shifted zeta pole; every convergence condition is proved. -/
theorem smoothDetector_contour_identity {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    {ρ : ℂ} (X : ℝ) {N q : ℝ} (hN : 0 < N) (hq : 0 ≤ q)
    (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re < 1) :
    (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      smoothDetectorKernel ψ ρ X N q (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)) =
        smoothDetectorResidue ψ ρ X N q +
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        smoothDetectorKernel ψ ρ X N q (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  let l : ℝ := 1/2-ρ.re
  let F := smoothDetectorKernel ψ ρ X N q
  let Jl : ℂ := ∫ t : ℝ, F ((l : ℂ)+(t : ℂ)*I)
  let Jr : ℂ := ∫ t : ℝ, F (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)
  let c : ℂ := 1/(2*Real.pi*I)
  have hl := intervalIntegral_tendsto_integral
    (integrable_smoothDetectorKernel_left hψ ha hb hs ρ X hN hq)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hr := intervalIntegral_tendsto_integral
    (integrable_smoothDetectorKernel_right hψ ha hb hs X hN hq hβ)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hbottom := tendsto_smoothDetector_horizontal_integral hψ ha hb hs X hN hq hβ hβ'.le
    (show |(-1 : ℝ)| = 1 by norm_num)
  have htop := tendsto_smoothDetector_horizontal_integral hψ ha hb hs X hN hq hβ hβ'.le
    (show |(1 : ℝ)| = 1 by norm_num)
  have hlim : Tendsto (fun R : ℝ => RectangleIntegral' F
      ((l : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I)) atTop
      (𝓝 (c*(I*Jr-I*Jl))) := by
    have h := (((hbottom.sub htop).add (hr.const_smul I)).sub (hl.const_smul I)).const_smul c
    simpa [RectangleIntegral',RectangleIntegral,HIntegral,VIntegral,F,l,Jl,Jr,c,smul_eq_mul] using h
  have heq : ∀ᶠ R : ℝ in atTop, RectangleIntegral' F
      ((l : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        smoothDetectorResidue ψ ρ X N q := by
    filter_upwards [eventually_gt_atTop |ρ.im|] with R hR
    exact smoothDetector_finite_rectangle_residue hψ ha hs hN hβ hβ' hR
  have he : c*(I*Jr-I*Jl) = smoothDetectorResidue ψ ρ X N q :=
    tendsto_nhds_unique hlim ((tendsto_congr' heq).mpr tendsto_const_nhds)
  change (((1/(2*Real.pi) : ℝ) : ℂ)*Jr) = smoothDetectorResidue ψ ρ X N q +
    (((1/(2*Real.pi) : ℝ) : ℂ)*Jl)
  rw [← he]
  dsimp [c]
  push_cast
  field_simp
  ring

end MathCollab.Density.Stronger
