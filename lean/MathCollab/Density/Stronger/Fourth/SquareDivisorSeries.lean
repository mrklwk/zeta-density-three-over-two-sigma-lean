module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance and adaptation details: third_party/twelfth/SQUARE_KERNEL_SERIES_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.SquareKernelFar
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem exists_zetaSquareRightKernel_uniform_gaussian_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t u : ℝ,
      ‖zetaSquareRightKernel t u‖ ≤
        C * Real.exp (100 - 100 * u ^ 2) * (3 + |t| + |u|) ^ 12 := by
  let G : ℝ := Real.pi ^ (-(3 / 2 : ℝ) / 2) * Real.Gamma ((3 / 2 : ℝ) / 2)
  have hG : 0 < G := mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by norm_num))
  let C : ℝ := 10000 * G ^ 2
  refine ⟨C, (by dsimp [C]; positivity), ?_⟩
  intro t u
  have hden := zetaSquarePoleNormalization_norm_lower t
  let w : ℂ := 1 + (u : ℂ) * I
  let s := afeCriticalPoint t + w
  let R : ℝ := 3 + |t| + |u|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg t, abs_nonneg u]
  have hwupper : ‖w‖ ≤ 1 + |u| := by
    simpa [w, Real.norm_eq_abs] using norm_add_le (1 : ℂ) ((u : ℂ) * I)
  have hwlower : 1 ≤ ‖w‖ := by
    simpa [w] using Complex.abs_re_le_norm w
  have hwR : ‖w‖ ≤ R := hwupper.trans (by dsimp [R]; linarith [abs_nonneg t])
  have hcrit (v : ℝ) : ‖afeCriticalPoint v‖ ≤ 1 / 2 + |v| := by
    simpa [afeCriticalPoint, Real.norm_eq_abs] using
      norm_add_le ((1 / 2 : ℝ) : ℂ) ((v : ℂ) * I)
  have hsR : ‖s‖ ≤ R := (norm_add_le _ _).trans (by
    dsimp [R]
    linarith [hcrit t])
  have hsubR : ‖1 - s‖ ≤ R := by
    have heq : 1 - s = afeCriticalPoint (-t) - w := by
      dsimp [s]
      rw [← one_sub_afeCriticalPoint]
      ring
    rw [heq]
    apply (norm_sub_le _ _).trans
    have hc := hcrit (-t)
    rw [abs_neg] at hc
    dsimp [R]
    linarith
  have hpoly : ‖(s * (1 - s)) ^ 2‖ ≤ R ^ 4 := by
    rw [norm_pow, norm_mul]
    calc
      _ ≤ (R * R) ^ 2 := by gcongr
      _ = R ^ 4 := by ring
  have haux := norm_hughesYoungAuxiliaryZero_le_polynomial hR hwR
  have hsre : s.re = 3 / 2 := by norm_num [s, w, afeCriticalPoint]
  have hgamma : ‖Complex.Gammaℝ s‖ ≤ G := by
    simpa only [hsre, G] using norm_GammaR_le_realGamma_re
      (show 0 < s.re by rw [hsre]; norm_num)
  have hexp : ‖Complex.exp (100 * w ^ 2)‖ = Real.exp (100 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [w, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  change ‖Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    (s * (1 - s)) ^ 2 * Complex.Gammaℝ s ^ 2 / zetaSquarePoleNormalization t / w‖ ≤ _
  simp only [norm_div, norm_mul, norm_pow, hexp]
  simp only [norm_pow, norm_mul] at hpoly
  calc
    _ ≤ (Real.exp (100 - 100 * u ^ 2) * (625 * R ^ 8) * R ^ 4 * G ^ 2 /
        (1 / 16)) / 1 := by gcongr
    _ = C * Real.exp (100 - 100 * u ^ 2) * R ^ 12 := by dsimp [C]; ring


/-- Fixed-height integrability of the literal unnormalized right kernel. -/
theorem integrable_zetaSquareRightKernel (t : ℝ) : Integrable (zetaSquareRightKernel t) := by
  obtain ⟨C,hC,hbound⟩ := exists_zetaSquareRightKernel_uniform_gaussian_bound
  let A : ℝ := 3+|t|
  let D : ℝ := Real.exp (12*A+36)
  have hpoly (u : ℝ) : (A+|u|)^12 ≤ D*Real.exp (u^2) := by
    have h := abs_polynomial_mul_exp_le_gaussian
      (by dsimp [A]; positivity : 0 ≤ A) (by norm_num : (0 : ℝ) ≤ 1) 0 12 u
    norm_num at h
    exact h
  have hpoint (u : ℝ) : ‖zetaSquareRightKernel t u‖ ≤
      (C*Real.exp 100*D)*Real.exp (-99*u^2) := by
    calc
      _ ≤ C*Real.exp (100-100*u^2)*(A+|u|)^12 := hbound t u
      _ ≤ C*Real.exp (100-100*u^2)*(D*Real.exp (u^2)) := by gcongr; exact hpoly u
      _ = _ := by
        rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg,
          show -(100*u^2) = -100*u^2 by ring]
        have hg : Real.exp (-100*u^2)*Real.exp (u^2) = Real.exp (-99*u^2) := by
          rw [← Real.exp_add]; congr 1; ring
        calc
          _ = (C*Real.exp 100*D)*(Real.exp (-100*u^2)*Real.exp (u^2)) := by ring
          _ = _ := by rw [hg]
  apply ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 99)).const_mul
    (C*Real.exp 100*D)).mono' (continuous_zetaSquareRightKernel t).aestronglyMeasurable
  exact Filter.Eventually.of_forall hpoint

theorem summable_divisorDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (divisorDirichletTerm s) := by
  exact divisorLSeries_summable hs

theorem tsum_divisorDirichletTerm (s : ℂ) :
    ∑' n : ℕ, divisorDirichletTerm s n =
      LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s := rfl

theorem continuous_divisorDirichletTerm_vertical
    (t c : ℝ) (n : ℕ) :
    Continuous (fun u : ℝ =>
      divisorDirichletTerm
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) n) := by
  by_cases hn : n = 0
  · subst n
    simpa [divisorDirichletTerm] using
      (continuous_const : Continuous (fun _u : ℝ => (0 : ℂ)))
  · simp only [divisorDirichletTerm, LSeries.term_of_ne_zero hn]
    exact continuous_const.div₀
      ((show Continuous (fun u : ℝ => afeCriticalPoint t + ((c : ℂ)+(u : ℂ)*I))
        from by fun_prop).const_cpow (Or.inl (by exact_mod_cast hn)))
      (fun _u => (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast hn))))

def zetaSquareDivisorTerm (t : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  divisorDirichletTerm (afeCriticalPoint t + (1 + (u : ℂ) * I)) n *
    zetaSquareRightKernel t u

theorem norm_zetaSquareDivisorTerm (t : ℝ) (n : ℕ) (u : ℝ) :
    ‖zetaSquareDivisorTerm t n u‖ =
      ‖divisorDirichletTerm (3 / 2) n‖ * ‖zetaSquareRightKernel t u‖ := by
  simp only [zetaSquareDivisorTerm, norm_mul, divisorDirichletTerm, LSeries.norm_term_eq]
  norm_num [afeCriticalPoint]

theorem integrable_zetaSquareDivisorTerm (t : ℝ) (n : ℕ) :
    Integrable (zetaSquareDivisorTerm t n) := by
  unfold zetaSquareDivisorTerm
  apply (integrable_zetaSquareRightKernel t).bdd_mul
    (c := ‖divisorDirichletTerm (3 / 2) n‖)
  · simpa using (continuous_divisorDirichletTerm_vertical t 1 n).aestronglyMeasurable
  · filter_upwards with u
    simp only [divisorDirichletTerm, LSeries.norm_term_eq]
    norm_num [afeCriticalPoint]

theorem integral_norm_zetaSquareDivisorTerm (t : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖zetaSquareDivisorTerm t n u‖) =
      ‖divisorDirichletTerm (3 / 2) n‖ * ∫ u : ℝ, ‖zetaSquareRightKernel t u‖ := by
  simp_rw [norm_zetaSquareDivisorTerm]
  exact integral_const_mul _ _

theorem summable_integral_norm_zetaSquareDivisorTerm (t : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖zetaSquareDivisorTerm t n u‖) := by
  simp_rw [integral_norm_zetaSquareDivisorTerm]
  exact (summable_divisorDirichletTerm (s := (3 / 2 : ℂ)) (by norm_num)).norm.mul_right _

theorem tsum_zetaSquareDivisorTerm (t u : ℝ) :
    (∑' n : ℕ, zetaSquareDivisorTerm t n u) =
      zetaSquareContourIntegrand t (1 + (u : ℂ) * I) := by
  simp only [zetaSquareDivisorTerm, tsum_mul_right, tsum_divisorDirichletTerm]
  rw [zetaSquareContourIntegrand_eq_rightKernel_mul_divisor, mul_comm]

def zetaSquareDivisorContribution (t : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, zetaSquareDivisorTerm t n u

/-- Tonelli on the complete line: the coefficientwise integrals form an
actual convergent series, not a prescribed value of an arbitrary sum. -/
theorem hasSum_zetaSquareDivisorContribution (t : ℝ) :
    HasSum (zetaSquareDivisorContribution t) (zetaSquareDivisorIntegral t) := by
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_zetaSquareDivisorTerm t) (summable_integral_norm_zetaSquareDivisorTerm t)
  simp_rw [tsum_zetaSquareDivisorTerm] at h
  change HasSum (fun n : ℕ => (1/(2*Real.pi) : ℂ)*∫ u : ℝ, zetaSquareDivisorTerm t n u)
    ((1/(2*Real.pi) : ℂ)*∫ u : ℝ,
      zetaSquareContourIntegrand t (((1 : ℝ) : ℂ)+(u : ℂ)*I))
  simpa only [Complex.ofReal_one] using h.mul_left (1/(2*Real.pi) : ℂ)

theorem completedZeta_square_eq_divisor_series (t : ℝ) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 =
      (∑' n : ℕ, zetaSquareDivisorContribution t n) +
        ∑' n : ℕ, zetaSquareDivisorContribution (-t) n := by
  rw [(hasSum_zetaSquareDivisorContribution t).tsum_eq,
    (hasSum_zetaSquareDivisorContribution (-t)).tsum_eq]
  exact completedZeta_square_eq_divisor_integrals t
def zetaSquareNormalizedContribution (t : ℝ) (n : ℕ) : ℂ :=
  (zetaSquareDivisorContribution t n + zetaSquareDivisorContribution (-t) n) /
    zetaSquareGammaNormalization t

theorem hasSum_zetaSquareNormalizedContribution (t : ℝ) :
    HasSum (zetaSquareNormalizedContribution t) ((zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) := by
  have h := ((hasSum_zetaSquareDivisorContribution t).add
    (hasSum_zetaSquareDivisorContribution (-t))).div_const (zetaSquareGammaNormalization t)
  rw [← completedZeta_square_eq_divisor_integrals,
    completedZeta_square_eq_norm_mul_gamma,
    mul_div_cancel_right₀ _ (zetaSquareGammaNormalization_ne_zero t)] at h
  exact h

theorem zetaSquareNorm_eq_divisor_series (t : ℝ) :
    zetaMomentCriticalNorm t ^ 2 = (∑' n : ℕ, zetaSquareNormalizedContribution t n).re := by
  rw [(hasSum_zetaSquareNormalizedContribution t).tsum_eq, Complex.ofReal_re]

end MathCollab.Density.Stronger.Fourth
