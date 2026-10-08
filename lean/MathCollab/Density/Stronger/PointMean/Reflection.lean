module
-- Reversible module-visibility port of the audited development.
/-
Selected actual displaced reflection proofs adapted from Scott McColm,
PointMeanReflection.lean and PointMeanOffCriticalStrong.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The Gamma quotient is proved at positive heights from the local digamma
error and Gronwall, keeping the exact coefficient of log(height).
-/
public import MathCollab.Density.Stronger.PointMean.GammaDisplacement
public import MathCollab.Density.Stronger.PointMean.OffCriticalPositive

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex
open MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

theorem norm_GammaR_real_im (r t : ℝ) :
    ‖Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ =
      Real.pi ^ (-r / 2) *
        ‖Complex.Gamma (((r / 2 : ℝ) : ℂ) +
          ((t / 2 : ℝ) : ℂ) * I)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  · congr 1
    simp
  · congr 2
    push_cast
    ring


theorem norm_GammaR_real_neg_im_eq (r t : ℝ) :
    ‖Complex.Gammaℝ ((r : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ := by
  rw [norm_GammaR_real_im, norm_GammaR_real_im]
  congr 1
  have hconj :
      (((r / 2 : ℝ) : ℂ) + (((-t) / 2 : ℝ) : ℂ) * I) =
        conj (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) := by
    simp only [map_add, map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  rw [hconj, Complex.Gamma_conj, norm_conj]



/-- Exact ordinary-zeta form of reflection between the two displaced lines. -/
theorem heathBrown_zeta_displaced_reflection
    {delta t : ℝ} (hdelta : 0 < delta) (hdeltaUpper : delta < 1 / 2) :
    riemannZeta
        (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I) =
      (Complex.Gammaℝ
          (((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
        Complex.Gammaℝ
          (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I)) *
        riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
  let sL : ℂ := ((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I
  let sR : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I
  have hsLRe : 0 < sL.re := by simp [sL]; linarith
  have hsRRe : 0 < sR.re := by simp [sR]; linarith
  have hOneSub : 1 - sL = sR := by
    apply Complex.ext <;> simp [sL, sR]
    ring
  have hFE := completedRiemannZeta_one_sub sL
  rw [hOneSub, completedRiemannZeta_eq_zeta_mul_GammaR hsRRe,
    completedRiemannZeta_eq_zeta_mul_GammaR hsLRe] at hFE
  have hGammaL : Complex.Gammaℝ sL ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hsLRe
  change riemannZeta sL =
    (Complex.Gammaℝ sR / Complex.Gammaℝ sL) * riemannZeta sR
  calc
    riemannZeta sL =
        (riemannZeta sL * Complex.Gammaℝ sL) / Complex.Gammaℝ sL := by
      field_simp
    _ = (riemannZeta sR * Complex.Gammaℝ sR) / Complex.Gammaℝ sL := by
      rw [hFE]
    _ = (Complex.Gammaℝ sR / Complex.Gammaℝ sL) * riemannZeta sR := by
      field_simp

/-- The archimedean quotient in the displaced functional equation. -/
theorem exists_norm_GammaR_heathBrown_reflection_ratio_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 4 ≤ t →
      ‖Complex.Gammaℝ
          (((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
        Complex.Gammaℝ
          (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp ((Real.log (t / 2 + 2) + C) * delta) := by
  obtain ⟨D, hD, hShift⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := (1 / 8 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro delta t hdelta hdeltaUpper ht
  let z : ℂ := (((1 / 2 - delta) / 2 : ℝ) : ℂ) +
    ((t / 2 : ℝ) : ℂ) * I
  have hzRe : z.re = (1 / 2 - delta) / 2 := by simp [z]
  have hzIm : |z.im| = t / 2 := by
    simp [z, abs_of_nonneg (by linarith : 0 ≤ t / 2)]
  have hzLower : (1 / 8 : ℝ) ≤ z.re := by rw [hzRe]; linarith
  have hzUpper : z.re + delta ≤ 1 := by rw [hzRe]; linarith
  have hGamma := hShift z delta hzLower hzUpper hdelta.le (by rw [hzIm]; linarith)
  have hzAdd : z + (delta : ℂ) =
      (((1 / 2 + delta) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [z]
    ring
  rw [hzAdd, hzIm] at hGamma
  have hGammaZ : 0 < ‖Complex.Gamma z‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [hzRe]; linarith)
  have hGammaRatio :
      ‖Complex.Gamma
          ((((1 / 2 + delta) / 2 : ℝ) : ℂ) +
            ((t / 2 : ℝ) : ℂ) * I)‖ /
        ‖Complex.Gamma
          ((((1 / 2 - delta) / 2 : ℝ) : ℂ) +
            ((t / 2 : ℝ) : ℂ) * I)‖ ≤
      Real.exp ((Real.log (t / 2 + 2) + D) * delta) := by
    have hzEq : z =
        (((1 / 2 - delta) / 2 : ℝ) : ℂ) +
          ((t / 2 : ℝ) : ℂ) * I := rfl
    rw [← hzEq]
    exact (div_le_iff₀ hGammaZ).2 (by simpa [mul_comm] using hGamma)
  have hPiPow : Real.pi ^ (-delta) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by linarith)
  rw [norm_div, norm_GammaR_real_neg_im_eq,
    norm_GammaR_real_im, norm_GammaR_real_im]
  have hPiDen : 0 < Real.pi ^ (-(1 / 2 - delta) / 2) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have hGammaDen : 0 < ‖Complex.Gamma
      ((((1 / 2 - delta) / 2 : ℝ) : ℂ) +
        ((t / 2 : ℝ) : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hPiRatio :
      Real.pi ^ (-(1 / 2 + delta) / 2) /
        Real.pi ^ (-(1 / 2 - delta) / 2) = Real.pi ^ (-delta) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg Real.pi_pos.le,
      ← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  calc
    (Real.pi ^ (-(1 / 2 + delta) / 2) *
        ‖Complex.Gamma
          ((((1 / 2 + delta) / 2 : ℝ) : ℂ) +
            ((t / 2 : ℝ) : ℂ) * I)‖) /
      (Real.pi ^ (-(1 / 2 - delta) / 2) *
        ‖Complex.Gamma
          ((((1 / 2 - delta) / 2 : ℝ) : ℂ) +
            ((t / 2 : ℝ) : ℂ) * I)‖) =
      Real.pi ^ (-delta) *
        (‖Complex.Gamma
            ((((1 / 2 + delta) / 2 : ℝ) : ℂ) +
              ((t / 2 : ℝ) : ℂ) * I)‖ /
          ‖Complex.Gamma
            ((((1 / 2 - delta) / 2 : ℝ) : ℂ) +
              ((t / 2 : ℝ) : ℂ) * I)‖) := by
        rw [← hPiRatio]
        field_simp [ne_of_gt hPiDen, ne_of_gt hGammaDen]
    _ ≤ 1 * Real.exp ((Real.log (t / 2 + 2) + D) * delta) := by
      exact mul_le_mul hPiPow hGammaRatio (by positivity) (by positivity)
    _ = Real.exp ((Real.log (t / 2 + 2) + D) * delta) := by ring

theorem exists_heathBrown_offCritical_minus_strong_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖riemannZeta
          (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * Real.exp (2 * (Real.log (t / 2 + 2) + D) * delta) *
          (1 + heathBrownStrongMellinCriticalMoment delta t) := by
  obtain ⟨P, hP, hPlus⟩ := exists_heathBrown_offCritical_plus_strong_le
  obtain ⟨D, hD, hRatio⟩ :=
    exists_norm_GammaR_heathBrown_reflection_ratio_le
  refine ⟨P, D, hP, hD, ?_⟩
  intro delta t hdelta hdeltaUpper ht
  let sP : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I
  let sR : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I
  let sL : ℂ := ((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I
  let q : ℂ := Complex.Gammaℝ sR / Complex.Gammaℝ sL
  have hReflect : riemannZeta sL = q * riemannZeta sR := by
    simpa only [sL, sR, q] using
      heathBrown_zeta_displaced_reflection hdelta (by linarith)
  have hsRConj : sR = conj sP := by
    apply Complex.ext <;> simp [sR, sP]
  have hZetaConj : ‖riemannZeta sR‖ = ‖riemannZeta sP‖ := by
    rw [hsRConj, _root_.riemannZeta_conj, norm_conj]
  have hq := hRatio delta t hdelta hdeltaUpper (by linarith)
  have hqSq : ‖q‖ ^ (2 : ℕ) ≤
      Real.exp (2 * (Real.log (t / 2 + 2) + D) * delta) := by
    have hp := pow_le_pow_left₀ (norm_nonneg q)
      (by simpa only [q, sR, sL] using hq) 2
    calc
      ‖q‖ ^ (2 : ℕ) ≤
          Real.exp ((Real.log (t / 2 + 2) + D) * delta) ^ (2 : ℕ) := hp
      _ = Real.exp (2 * (Real.log (t / 2 + 2) + D) * delta) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hplus := hPlus delta t hdelta hdeltaUpper ht
  change ‖riemannZeta sL‖ ^ (2 : ℕ) ≤ _
  rw [hReflect, norm_mul, mul_pow, hZetaConj]
  calc
    ‖q‖ ^ (2 : ℕ) * ‖riemannZeta sP‖ ^ (2 : ℕ) ≤
        Real.exp (2 * (Real.log (t / 2 + 2) + D) * delta) *
          (P * (1 + heathBrownStrongMellinCriticalMoment delta t)) := by
      exact mul_le_mul hqSq (by simpa only [sP] using hplus)
        (by positivity) (by positivity)
    _ = P * Real.exp (2 * (Real.log (t / 2 + 2) + D) * delta) *
          (1 + heathBrownStrongMellinCriticalMoment delta t) := by ring

end MathCollab.Density.Stronger.PointMean
