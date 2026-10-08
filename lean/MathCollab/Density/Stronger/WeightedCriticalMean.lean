module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothBlockContour

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

def weightedCriticalMean (A : ℕ) (γ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+((γ+t : ℝ) : ℂ)*I)‖/(1+|t|)^A

theorem integrable_weightedCriticalMean (A : ℕ) (hA : 3 ≤ A) (γ : ℝ) :
    Integrable (fun t : ℝ => ‖riemannZeta ((1/2 : ℂ)+((γ+t : ℝ) : ℂ)*I)‖/(1+|t|)^A) := by
  have hc : Continuous (fun t : ℝ => ‖riemannZeta ((1/2 : ℂ)+((γ+t : ℝ) : ℂ)*I)‖/(1+|t|)^A) := by
    apply Continuous.div
    · apply Continuous.norm
      apply continuous_iff_continuousAt.mpr
      intro t
      apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt (by fun_prop)
      intro he
      have hh := congrArg Complex.re he
      norm_num at hh
    · fun_prop
    · intro t; positivity
  have hmajor : Integrable (fun t : ℝ => (4*(1+|γ|))*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply hmajor.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_of_nonneg (by positivity : 0 ≤
    ‖riemannZeta ((1/2 : ℂ)+((γ+t : ℝ) : ℂ)*I)‖/(1+|t|)^A)]
  have hzt := norm_riemannZeta_critical_le_linear (γ+t)
  have hz : ‖riemannZeta ((1/2 : ℂ)+((γ+t : ℝ) : ℂ)*I)‖ ≤ 4*(1+|γ|)*(1+|t|) := by
    have hab := abs_add_le γ t
    nlinarith [mul_nonneg (abs_nonneg γ) (abs_nonneg t)]
  have hp : (1+|t|)^3 ≤ (1+|t|)^A := pow_le_pow_right₀ (by linarith [abs_nonneg t]) hA
  calc
    _ ≤ (4*(1+|γ|)*(1+|t|))/(1+|t|)^3 := by
      exact div_le_div₀ (by positivity) hz (by positivity) hp
    _ = (4*(1+|γ|))/(1+|t|)^2 := by field_simp
    _ ≤ (4*(1+|γ|))*(1+t^2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_abs t, abs_nonneg t]

theorem weightedCriticalMean_nonneg (A : ℕ) (γ : ℝ) : 0 ≤ weightedCriticalMean A γ :=
  integral_nonneg (fun t => by positivity)

/-- Integrating the actual kernel preserves the sharp square-root mollifier
factor and the exact scale exponent. -/
theorem uniform_smoothDetector_critical_integral_bound {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℂ) (X N q : ℝ),
      3/4 ≤ ρ.re → ρ.re ≤ 1 → 0 ≤ X → 0 < N → 0 ≤ q →
      ‖∫ t : ℝ, smoothDetectorKernel ψ ρ X N q
        (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)‖ ≤
          C*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im := by
  obtain ⟨C,hC,h⟩ := uniform_smoothDetectorKernel_critical_bound hψ ha hb hs A
  refine ⟨C,hC,?_⟩
  intro ρ X N q hβ hβ' hX hN hq
  have hK := integrable_smoothDetectorKernel_left hψ ha hb hs ρ X hN hq
  have hJ := (integrable_weightedCriticalMean A hA ρ.im).const_mul (C*Real.sqrt X*N^(1/2-ρ.re))
  calc
    _ ≤ ∫ t : ℝ, ‖smoothDetectorKernel ψ ρ X N q
        (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (C*Real.sqrt X*N^(1/2-ρ.re)) *
        (‖riemannZeta ((1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I)‖/(1+|t|)^A) := by
      apply integral_mono hK.norm hJ
      intro t
      simpa only [mul_div_assoc] using h ρ X N q t hβ hβ' hX hN hq
    _ = _ := by rw [integral_const_mul]; rfl

theorem uniform_smoothMollifierBlock_mean_bound {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℂ) (X N q : ℝ),
      3/4 ≤ ρ.re → ρ.re < 1 → 0 ≤ X → 0 < N → 0 ≤ q →
      ‖smoothMollifierBlock ψ ρ X N q‖ ≤ ‖smoothDetectorResidue ψ ρ X N q‖ +
        C*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im := by
  obtain ⟨C,hC,h⟩ := uniform_smoothDetector_critical_integral_bound hψ ha hb hs A hA
  let c : ℂ := ((1/(2*Real.pi) : ℝ) : ℂ)
  refine ⟨‖c‖*C, by positivity, ?_⟩
  intro ρ X N q hβ hβ' hX hN hq
  rw [smoothMollifierBlock_contour_identity hψ ha hb hs X hN hq hβ hβ']
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_mul]
  have hh := mul_le_mul_of_nonneg_left (h ρ X N q hβ hβ'.le hX hN hq) (norm_nonneg c)
  simpa only [mul_assoc] using hh

end MathCollab.Density.Stronger
