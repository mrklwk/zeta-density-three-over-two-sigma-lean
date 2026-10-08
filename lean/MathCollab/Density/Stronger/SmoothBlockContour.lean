module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothDetector
public import MathCollab.Density.Stronger.SmoothContourIdentity
public import MathCollab.Density.MollifierBound

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Actual block identity after the second contour shift. Both the series
representation and all contour convergence conditions are discharged. -/
theorem smoothMollifierBlock_contour_identity {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    {ρ : ℂ} (X : ℝ) {N q : ℝ} (hN : 0 < N) (hq : 0 ≤ q)
    (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re < 1) :
    smoothMollifierBlock ψ ρ X N q = smoothDetectorResidue ψ ρ X N q +
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        smoothDetectorKernel ψ ρ X N q (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  rw [smoothMollifierBlock_eq_rightContour hψ ha hb hs hN q X hβ]
  exact smoothDetector_contour_identity hψ ha hb hs X hN hq hβ hβ'

/-- The actual detecting dyadic block, with q=N/Y and the n=1 term already
removed, is represented on the critical line plus its exact residue. -/
theorem smoothDetectorBlock_contour_identity {ρ : ℂ} (X : ℝ) {Y : ℝ} {j : ℤ}
    (hY : 0 < Y) (hN : 2 ≤ (2 : ℝ)^j)
    (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re < 1) :
    smoothDetectorBlock ρ X Y j =
      smoothDetectorResidue smoothDyadicWeight ρ X ((2 : ℝ)^j) ((2 : ℝ)^j/Y) +
        (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
          smoothDetectorKernel smoothDyadicWeight ρ X ((2 : ℝ)^j) ((2 : ℝ)^j/Y)
            (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  rw [smoothDetectorBlock_eq_smoothMollifierBlock X hY (by linarith) hN]
  exact smoothMollifierBlock_contour_identity smoothDyadicWeight_contDiff
    (by norm_num : (0:ℝ)<5/8) (by norm_num : (0:ℝ)<3/2) smoothDyadicWeight_tsupport
    X (zpow_pos (by norm_num) _) (by positivity) hβ hβ'

/-- Arbitrary-order uniform decay of the genuine zeta-pole residue. The
constant precedes the cutoff, scale, damping parameter, and zero coordinates. -/
theorem uniform_smoothDetectorResidue_bound {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℂ) (X N q : ℝ),
      3/4 ≤ ρ.re → ρ.re ≤ 1 → 0 ≤ X → 0 < N → 0 ≤ q →
      ‖smoothDetectorResidue ψ ρ X N q‖ ≤
        C*Real.sqrt X*N^(1-ρ.re)/(1+|ρ.im|)^A := by
  obtain ⟨B,hB,h⟩ := dampedCutoff_uniform_mellin_decay hψ ha hb hs 0 (1/4) A
  refine ⟨2*B, by positivity, ?_⟩
  intro ρ X N q hβ hβ' hX hN hq
  have hm := h (1-ρ.re) ⟨by linarith,by linarith⟩ q hq (-ρ.im)
  have he : ((1-ρ.re : ℝ) : ℂ)+(-ρ.im : ℝ)*I = 1-ρ := by
    apply Complex.ext <;> simp
  rw [he, abs_neg] at hm
  have hM := norm_zetaMollifier_le_two_sqrt (s := 1) hX (by norm_num)
  rw [smoothDetectorResidue, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ (N^(1-ρ.re)*(B/(1+|ρ.im|)^A))*(2*Real.sqrt X) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hM
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The critical-line integrand has the square-root mollifier
factor and exact N exponent, uniformly before every zero, scale and frequency. -/
theorem uniform_smoothDetectorKernel_critical_bound {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℂ) (X N q t : ℝ),
      3/4 ≤ ρ.re → ρ.re ≤ 1 → 0 ≤ X → 0 < N → 0 ≤ q →
      ‖smoothDetectorKernel ψ ρ X N q (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)‖ ≤
        C*Real.sqrt X*N^(1/2-ρ.re)*
          ‖riemannZeta ((1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I)‖/(1+|t|)^A := by
  obtain ⟨B,hB,h⟩ := dampedCutoff_uniform_mellin_decay hψ ha hb hs (-1/2) (-1/4) A
  refine ⟨2*B, by positivity, ?_⟩
  intro ρ X N q t hβ hβ' hX hN hq
  have hm := h (1/2-ρ.re) ⟨by linarith,by linarith⟩ q hq t
  have he : ρ+(((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I) =
      (1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp
  have hM := norm_zetaMollifier_le_two_sqrt
    (s := ρ+(((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) hX (by simp)
  rw [smoothDetectorKernel, norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ ((N^(1/2-ρ.re)*(B/(1+|t|)^A))*(2*Real.sqrt X))*
        ‖riemannZeta (ρ+(((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I))‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hM
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [he]; ring

end MathCollab.Density.Stronger
