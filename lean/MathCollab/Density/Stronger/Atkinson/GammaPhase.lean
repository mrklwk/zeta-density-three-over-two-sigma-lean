module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Provenance: ../../../../../third_party/twelfth/ATKINSON_GAUSSIAN_MANIFEST.json.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import Mathlib.Analysis.Calculus.Deriv.Star
public import MathCollab.Density.Stronger.Fourth.GammaShiftLog
public import MathCollab.Density.Stronger.Fourth.SquareNormalized

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory
open scoped ComplexConjugate
open MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Stronger.Fourth.Digamma
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem digamma_conj (z : ℂ) :
    Complex.digamma (conj z) = conj (Complex.digamma z) := by
  have hGamma : conj ∘ Complex.Gamma ∘ conj = Complex.Gamma := by
    funext w
    simp [Function.comp_apply, Complex.Gamma_conj]
  have hd : deriv Complex.Gamma (conj z) = conj (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hGamma, deriv_conj_conj]
    simp [Function.comp_apply]
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, hd,
    Complex.Gamma_conj, ← map_div₀]

def zetaSquareReflectedGammaPhase (t : ℝ) : ℂ :=
  Complex.Gammaℝ (afeCriticalPoint (-t)) / Complex.Gammaℝ (afeCriticalPoint t)

def zetaSquareGammaFrequency (t : ℝ) : ℝ :=
  Real.log Real.pi - (Complex.digamma (afeCriticalPoint t / 2)).re

theorem norm_zetaSquareReflectedGammaPhase (t : ℝ) :
    ‖zetaSquareReflectedGammaPhase t‖ = 1 := by
  rw [zetaSquareReflectedGammaPhase, afeCriticalPoint_neg_eq_star]
  change ‖Complex.Gammaℝ (conj (afeCriticalPoint t)) / Complex.Gammaℝ (afeCriticalPoint t)‖ = 1
  rw [gammaReal_conj, norm_div, Complex.norm_conj, div_self]
  exact norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint]))

theorem zetaSquareReflectedGammaPhase_zero : zetaSquareReflectedGammaPhase 0 = 1 := by
  simp only [zetaSquareReflectedGammaPhase, neg_zero]
  exact div_self (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint]))

/-- This is the actual functional-equation phase of the zeta source. -/
theorem zetaSquareReflectedGammaPhase_mul_zeta (t : ℝ) :
    zetaSquareReflectedGammaPhase t * riemannZeta (afeCriticalPoint (-t)) =
      riemannZeta (afeCriticalPoint t) := by
  have hreflect : completedRiemannZeta (afeCriticalPoint (-t)) =
      completedRiemannZeta (afeCriticalPoint t) := by
    rw [← one_sub_afeCriticalPoint, completedRiemannZeta_one_sub]
  rw [completedRiemannZeta_eq_zeta_mul_GammaR (by norm_num [afeCriticalPoint]),
    completedRiemannZeta_eq_zeta_mul_GammaR (by norm_num [afeCriticalPoint])] at hreflect
  unfold zetaSquareReflectedGammaPhase
  have hne := Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint] :
    0 < (afeCriticalPoint t).re)
  rw [div_mul_eq_mul_div, mul_comm (Complex.Gammaℝ _) _, hreflect]
  exact mul_div_cancel_right₀ _ hne

/-- Factor the exact Gamma normalization in the reflected contour branch. -/
theorem zetaSquareGammaNormalization_reflected_factor (t : ℝ) (w : ℂ) :
    Complex.Gammaℝ (afeCriticalPoint (-t) + w) ^ 2 / zetaSquareGammaNormalization t =
      zetaSquareReflectedGammaPhase t *
        (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
          Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2 := by
  have hplus := Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint] :
    0 < (afeCriticalPoint t).re)
  have hminus := Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint] :
    0 < (afeCriticalPoint (-t)).re)
  unfold zetaSquareGammaNormalization zetaSquareReflectedGammaPhase
  field_simp

private theorem hasDerivAt_gammaCritical (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.Gammaℝ (afeCriticalPoint u))
      (Complex.Gammaℝ (afeCriticalPoint t) *
        ((-Complex.log (Real.pi : ℂ) + Complex.digamma (afeCriticalPoint t / 2)) / 2) * I) t := by
  have hinner : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + z * I) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (1 / 2 : ℂ)
  exact ((hasDerivAt_gammaReal (by norm_num [afeCriticalPoint])).comp (t : ℂ) hinner).comp_ofReal

/-- Exact phase differential equation, with a real-valued frequency. -/
theorem hasDerivAt_zetaSquareReflectedGammaPhase (t : ℝ) :
    HasDerivAt zetaSquareReflectedGammaPhase
      (I * (zetaSquareGammaFrequency t : ℂ) * zetaSquareReflectedGammaPhase t) t := by
  have hminus := (hasDerivAt_gammaCritical (-t)).scomp t (hasDerivAt_neg t)
  have hplus := hasDerivAt_gammaCritical t
  have hne := Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint] :
    0 < (afeCriticalPoint t).re)
  have hpsi : Complex.digamma (afeCriticalPoint (-t) / 2) =
      conj (Complex.digamma (afeCriticalPoint t / 2)) := by
    rw [afeCriticalPoint_neg_eq_star]
    change Complex.digamma (conj (afeCriticalPoint t) / 2) = _
    simpa only [map_div₀, map_ofNat] using digamma_conj (afeCriticalPoint t / 2)
  have hsum : Complex.digamma (afeCriticalPoint (-t) / 2) +
      Complex.digamma (afeCriticalPoint t / 2) =
      2 * ((Complex.digamma (afeCriticalPoint t / 2)).re : ℂ) := by
    rw [hpsi, add_comm, Complex.add_conj]
    push_cast
    rfl
  convert hminus.div hplus hne using 1
  · rfl
  · unfold zetaSquareGammaFrequency zetaSquareReflectedGammaPhase
    simp only [Function.comp_apply, neg_smul, one_smul]
    rw [Complex.ofReal_sub, Complex.ofReal_log Real.pi_pos.le]
    field_simp
    linear_combination Complex.Gammaℝ (afeCriticalPoint (-t)) * hsum

/-- Sharp leading frequency, derived from the actual digamma function. -/
theorem abs_zetaSquareGammaFrequency_add_log_le {t : ℝ} (ht : 2 ≤ t) :
    |zetaSquareGammaFrequency t + Real.log (t / (2 * Real.pi))| ≤ 9 / t := by
  have ht0 : 0 < t := by linarith
  have heq : (afeCriticalPoint t / 2).im = t / 2 := by simp [afeCriticalPoint]
  have hre : (afeCriticalPoint t / 2).re = 1 / 4 := by norm_num [afeCriticalPoint]
  have h := abs_re_digamma_sub_log_im_le (z := afeCriticalPoint t / 2)
    (by rw [hre]; norm_num) (by rw [heq, abs_of_pos (div_pos ht0 two_pos)]; linarith)
  rw [heq, hre, abs_of_pos (div_pos ht0 two_pos)] at h
  have hlogs : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [← div_div, Real.log_div (ne_of_gt (div_pos ht0 two_pos)) Real.pi_ne_zero]
  rw [zetaSquareGammaFrequency, hlogs]
  have habs : |Real.log Real.pi - (Complex.digamma (afeCriticalPoint t / 2)).re +
      (Real.log (t / 2) - Real.log Real.pi)| =
      |(Complex.digamma (afeCriticalPoint t / 2)).re - Real.log (t / 2)| := by
    rw [show Real.log Real.pi - (Complex.digamma (afeCriticalPoint t / 2)).re +
      (Real.log (t / 2) - Real.log Real.pi) =
      -((Complex.digamma (afeCriticalPoint t / 2)).re - Real.log (t / 2)) by ring, abs_neg]
  rw [habs]
  refine h.trans ?_
  field_simp
  norm_num

end MathCollab.Density.Stronger.Atkinson
