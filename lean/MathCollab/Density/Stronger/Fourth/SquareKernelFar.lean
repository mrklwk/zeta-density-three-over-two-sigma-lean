module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance and adaptation details: third_party/twelfth/SQUARE_KERNEL_SERIES_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.SquareNormalized

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex
open MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem abs_polynomial_mul_exp_le_gaussian
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (D : ℝ) (m : ℕ) (u : ℝ) :
    (a+b*|u|)^m * Real.exp (D*|u|) ≤
      Real.exp ((m:ℝ)*a+((m:ℝ)*b+D)^2/4) * Real.exp (u^2) := by
  have hx : 0 ≤ a+b*|u| := by positivity
  have he : a+b*|u| ≤ Real.exp (a+b*|u|) := by
    linarith [Real.add_one_le_exp (a+b*|u|)]
  calc
    _ ≤ (Real.exp (a+b*|u|))^m * Real.exp (D*|u|) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx he m) (by positivity)
    _ = Real.exp ((m:ℝ)*(a+b*|u|)+D*|u|) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (((m:ℝ)*a+((m:ℝ)*b+D)^2/4)+u^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (|u|-((m:ℝ)*b+D)/2), sq_abs u]
    _ = _ := Real.exp_add _ _

theorem norm_vertical_shift_le {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    ‖(c:ℂ)+(u:ℂ)*I‖ ≤ c+|u| := by
  simpa only [norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc] using
      norm_add_le (c:ℂ) ((u:ℂ)*I)

theorem vertical_shift_re_le_norm {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    c ≤ ‖(c:ℂ)+(u:ℂ)*I‖ := by
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, abs_of_nonneg hc] using
      Complex.abs_re_le_norm ((c:ℂ)+(u:ℂ)*I)
theorem norm_complex_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have hraw : ‖(2 : ℂ) * Complex.sin z‖ ≤
      Real.exp z.im + Real.exp (-z.im) := by
    rw [Complex.two_sin]
    calc
      _ = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ := by simp
      _ ≤ ‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖ := norm_sub_le _ _
      _ = _ := by rw [Complex.norm_exp, Complex.norm_exp]; simp
  simp only [norm_mul, Complex.norm_ofNat] at hraw
  have hplus := Real.exp_le_exp.mpr (le_abs_self z.im)
  have hminus := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith

theorem norm_inv_gamma_critical_half_le (t : ℝ) :
    ‖(Complex.Gamma (afeCriticalPoint t / 2))⁻¹‖ ≤
      (Real.Gamma (3 / 4) / Real.pi) * Real.exp (Real.pi * |t| / 2) := by
  let p := afeCriticalPoint t / 2
  have hp : 0 < p.re := by norm_num [p, afeCriticalPoint]
  have hq : 0 < (1 - p).re := by norm_num [p, afeCriticalPoint]
  have hGp : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hp
  have hGq : Complex.Gamma (1 - p) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hq
  have href := Complex.Gamma_mul_Gamma_one_sub p
  have hsin : Complex.sin ((Real.pi : ℂ) * p) ≠ 0 := by
    intro h
    rw [h, div_zero] at href
    exact mul_ne_zero hGp hGq href
  have hid : (Complex.Gamma p)⁻¹ =
      Complex.Gamma (1 - p) * Complex.sin ((Real.pi : ℂ) * p) / (Real.pi : ℂ) := by
    have h := (eq_div_iff hsin).mp href
    rw [mul_comm (Real.pi : ℂ) p] at h
    field_simp
    linear_combination -h
  have hg : ‖Complex.Gamma (1 - p)‖ ≤ Real.Gamma (3 / 4) := by
    convert norm_Gamma_le_realGamma_re hq using 1
    norm_num [p, afeCriticalPoint]
  have hs : ‖Complex.sin ((Real.pi : ℂ) * p)‖ ≤ Real.exp (Real.pi * |t| / 2) := by
    have h := norm_complex_sin_le_exp_abs_im ((Real.pi : ℂ) * p)
    simpa [p, afeCriticalPoint, abs_mul, abs_div, abs_of_pos Real.pi_pos, mul_div_assoc] using h
  change ‖(Complex.Gamma p)⁻¹‖ ≤ _
  rw [hid, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (Real.Gamma (3 / 4) * Real.exp (Real.pi * |t| / 2)) / Real.pi := by gcongr
    _ = _ := by ring

theorem exists_norm_inv_gammaReal_critical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(Complex.Gammaℝ (afeCriticalPoint t))⁻¹‖ ≤ C * Real.exp (Real.pi * |t| / 2) := by
  let P : ℝ := Real.pi ^ (-(1 / 4 : ℝ))
  have hP : 0 < P := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨P⁻¹ * (Real.Gamma (3 / 4) / Real.pi),
    mul_pos (inv_pos.mpr hP) (div_pos (Real.Gamma_pos_of_pos (by norm_num)) Real.pi_pos), ?_⟩
  intro t
  have hn : ‖Complex.Gammaℝ (afeCriticalPoint t)‖ = P * ‖Complex.Gamma (afeCriticalPoint t / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    norm_num [afeCriticalPoint, P]
  rw [norm_inv, hn, mul_inv_rev]
  have h := mul_le_mul_of_nonneg_left (norm_inv_gamma_critical_half_le t) (inv_nonneg.mpr hP.le)
  rw [norm_inv] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- One height-independent constant for the exact normalization used by
the source identity, including height zero and both signs of the height. -/
theorem exists_norm_inv_zetaSquareGammaNormalization_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(zetaSquareGammaNormalization t)⁻¹‖ ≤ C * Real.exp (Real.pi * |t|) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_inv_gammaReal_critical_le
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro t
  rw [zetaSquareGammaNormalization, mul_inv_rev, norm_mul]
  have hminus := hbound (-t)
  rw [abs_neg] at hminus
  calc
    _ ≤ (C * Real.exp (Real.pi * |t| / 2)) * (C * Real.exp (Real.pi * |t| / 2)) :=
      mul_le_mul hminus (hbound t) (norm_nonneg _) (by positivity)
    _ = C ^ 2 * (Real.exp (Real.pi * |t| / 2) * Real.exp (Real.pi * |t| / 2)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring
theorem norm_zetaSquarePoleShift_le_polynomial
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) (u : ℝ) :
    ‖zetaSquarePoleShift t ((c:ℂ)+(u:ℂ)*I)‖ ≤
      16*(3+c+t+|u|)^4 := by
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let s : ℂ := afeCriticalPoint (-t)+w
  let R : ℝ := 3+c+t+|u|
  have hcrit : ‖afeCriticalPoint (-t)‖ ≤ 1/2+t := by
    simpa [afeCriticalPoint,abs_of_nonneg ht] using
      norm_add_le (1/2:ℂ) (((-t:ℝ):ℂ)*I)
  have hw : ‖w‖ ≤ c+|u| := norm_vertical_shift_le hc u
  have hs : ‖s‖ ≤ 1/2+t+c+|u| :=
    (norm_add_le _ _).trans (by linarith)
  have hsR : ‖s‖ ≤ R := hs.trans (by dsimp [R]; linarith)
  have hsub : ‖1-s‖ ≤ R := (norm_sub_le _ _).trans (by
    rw [norm_one]
    dsimp [R]
    linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  rw [zetaSquarePoleShift_eq_source, norm_div, norm_pow, norm_mul]
  change (‖s‖*‖1-s‖)^2/‖zetaSquarePoleNormalization t‖ ≤ 16*R^4
  calc
    _ ≤ (R*R)^2/(1/16) := by
      gcongr
      exact zetaSquarePoleNormalization_norm_lower t
    _ = _ := by ring

theorem exists_norm_zetaFourthKernel_far_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      0 ≤ t → t ≤ 4*|u| →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*Real.exp (-99*u^2) := by
  obtain ⟨C,hC,hInv⟩ := exists_norm_inv_zetaSquareGammaNormalization_le
  let G : ℝ := Real.pi^(-(1/2+c)/2)*Real.Gamma ((1/2+c)/2)
  have hG : 0 < G := mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by linarith))
  let A : ℝ := 10000*G^2*C/c
  let Q : ℝ := 12*(c+3)+(60+4*Real.pi)^2/4
  let K : ℝ := A*Real.exp (100*c^2)*Real.exp Q
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro t u ht hu
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let R : ℝ := 3+c+t+|u|
  let B : ℝ := c+3+5*|u|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg u]
  have hw := norm_vertical_shift_le hc.le u
  have hwlower := vertical_shift_re_le_norm hc.le u
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625*R^8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR (hw.trans (by dsimp [R]; linarith))
  have hpole : ‖zetaSquarePoleShift t w‖ ≤ 16*R^4 :=
    norm_zetaSquarePoleShift_le_polynomial ht hc.le u
  have hg : ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)‖ ≤ G := by
    have hre : (afeCriticalPoint (-t)+w).re = 1/2+c := by
      norm_num [afeCriticalPoint,w]
    simpa only [hre,G] using norm_GammaR_le_realGamma_re
      (show 0 < (afeCriticalPoint (-t)+w).re by rw [hre]; linarith)
  have hgamma :
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤
        G^2*(C*Real.exp (Real.pi*t)) := by
    rw [← norm_gammaSquare_div_zetaSquareGammaNormalization,
      div_eq_mul_inv, norm_mul, norm_pow]
    have hi := hInv t
    rw [abs_of_nonneg ht] at hi
    gcongr
  have hRB : R ≤ B := by dsimp [R,B]; linarith
  have hpoly : B^12*Real.exp ((4*Real.pi)*|u|) ≤ Real.exp Q*Real.exp (u^2) := by
    have hp := abs_polynomial_mul_exp_le_gaussian
      (by linarith : 0 ≤ c+3) (by norm_num : (0:ℝ) ≤ 5) (4*Real.pi) 12 u
    norm_num at hp
    exact hp
  have htime : Real.exp (Real.pi*t) ≤ Real.exp ((4*Real.pi)*|u|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hu Real.pi_pos.le]
  have he : Real.exp (100*c^2-100*u^2) =
      Real.exp (100*c^2)*Real.exp (-100*u^2) := by rw [← Real.exp_add]; congr 1; ring
  have hgauss : Real.exp (u^2)*Real.exp (-100*u^2) = Real.exp (-99*u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_zetaFourthKernel_vertical]
  change Real.exp (100*c^2-100*u^2)*‖hughesYoungAuxiliaryZero w‖*
    ‖zetaSquarePoleShift t w‖*
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
      Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖/‖w‖ ≤ _
  calc
    _ ≤ Real.exp (100*c^2-100*u^2)*(625*R^8)*(16*R^4)*
        (G^2*(C*Real.exp (Real.pi*t)))/c := by gcongr
    _ = A*R^12*Real.exp (100*c^2-100*u^2)*Real.exp (Real.pi*t) := by dsimp [A]; ring
    _ ≤ A*B^12*Real.exp (100*c^2-100*u^2)*Real.exp ((4*Real.pi)*|u|) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hRB 12) hA.le)
          (Real.exp_pos _).le)
        htime (Real.exp_pos _).le (by positivity)
    _ = A*Real.exp (100*c^2)*
        (B^12*Real.exp ((4*Real.pi)*|u|))*Real.exp (-100*u^2) := by rw [he]; ring
    _ ≤ A*Real.exp (100*c^2)*(Real.exp Q*Real.exp (u^2))*Real.exp (-100*u^2) := by
      gcongr
    _ = K*(Real.exp (u^2)*Real.exp (-100*u^2)) := by dsimp [K]; ring
    _ = _ := by rw [hgauss]

end MathCollab.Density.Stronger.Fourth
