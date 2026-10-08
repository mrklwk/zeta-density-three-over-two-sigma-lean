module
-- Reversible module-visibility port of the audited development.
/- Narrow actual normalized-zeta source and kernel port from Scott McColm,
MIT-0, exact pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SQUARE_NORMALIZED_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0. -/
public import MathCollab.Density.Stronger.Fourth.SquareContour

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped ComplexConjugate Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem gammaReal_conj (z : ℂ) : Complex.Gammaℝ (conj z) = conj (Complex.Gammaℝ z) := by
  have hpow := Complex.cpow_conj (Real.pi : ℂ) (-z / 2)
    (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm)
  simp only [map_div₀, map_neg, map_ofNat, conj_ofReal] at hpow
  simp only [Complex.Gammaℝ, map_mul, ← Complex.Gamma_conj,
    map_div₀, map_ofNat, hpow]


theorem continuous_GammaR_afe_vertical
    (t : ℝ) {c : ℝ} (hc : 0 < 1 / 2 + c) :
    Continuous (fun u : ℝ =>
      Complex.Gammaℝ
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) := by
  rw [continuous_iff_continuousAt]
  intro u
  unfold Complex.Gammaℝ
  apply ContinuousAt.mul
  · exact (continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp (by fun_prop)
  · apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      simp [afeCriticalPoint] at hre
      linarith


def zetaSquareRightKernel (t u : ℝ) : ℂ :=
  let w : ℂ := 1 + (u : ℂ) * I
  let s := afeCriticalPoint t + w
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    (s * (1 - s)) ^ 2 * Complex.Gammaℝ s ^ 2 /
    zetaSquarePoleNormalization t / w

theorem continuous_zetaSquareRightKernel (t : ℝ) :
    Continuous (zetaSquareRightKernel t) := by
  have hGamma : Continuous (fun u : ℝ =>
      Complex.Gammaℝ (afeCriticalPoint t + (1 + (u : ℂ) * I))) := by
    simpa using continuous_GammaR_afe_vertical t (c := 1) (by norm_num)
  have hw : ∀ u : ℝ, (1 : ℂ) + (u : ℂ) * I ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    norm_num at this
  unfold zetaSquareRightKernel
  dsimp only
  have haux := differentiable_hughesYoungAuxiliaryZero.continuous
  apply Continuous.div ?_ (by fun_prop) hw
  apply Continuous.div_const
  fun_prop (disch := assumption)


theorem zetaSquareContourIntegrand_eq_rightKernel_mul_divisor (t u : ℝ) :
    zetaSquareContourIntegrand t (1 + (u : ℂ) * I) =
      zetaSquareRightKernel t u *
        LSeries (fun n : ℕ => (n.divisors.card : ℂ))
          (afeCriticalPoint t + (1 + (u : ℂ) * I)) := by
  let w : ℂ := 1 + (u : ℂ) * I
  let s := afeCriticalPoint t + w
  have hsre : 1 < s.re := by norm_num [s, w, afeCriticalPoint]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold zetaSquareContourIntegrand zetaSquareContourNumerator zetaSquareRightKernel
  change (Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w * completedXiNumerator s ^ 2 /
    zetaSquarePoleNormalization t) / w = _
  rw [completedXiNumerator_eq s hs0 hs1,
    completedRiemannZeta_eq_zeta_mul_GammaR (zero_lt_one.trans hsre)]
  simp only [mul_pow]
  rw [riemannZeta_sq_eq_divisorLSeries hsre]
  ring

theorem zetaSquareRightKernel_conj (t u : ℝ) :
    zetaSquareRightKernel (-t) (-u) = conj (zetaSquareRightKernel t u) := by
  have hw : (1 : ℂ) + ((-u : ℝ) : ℂ) * I = conj (1 + (u : ℂ) * I) := by simp
  have hs : afeCriticalPoint (-t) = conj (afeCriticalPoint t) := afeCriticalPoint_neg_eq_star t
  unfold zetaSquareRightKernel
  dsimp only
  rw [hw, hs, ← map_add, gammaReal_conj]
  simp only [hughesYoungAuxiliaryZero, zetaSquarePoleNormalization_eq,
    map_div₀, map_mul, map_pow, map_sub, map_ofNat, map_one, conj_ofReal, ← Complex.exp_conj]
  simp only [neg_sq]


def zetaSquareDivisorIntegral (t : ℝ) : ℂ := zetaSquareVerticalIntegral t 1

theorem completedZeta_square_eq_divisor_integrals (t : ℝ) :
    completedRiemannZeta (afeCriticalPoint t)^2 =
      zetaSquareDivisorIntegral t + zetaSquareDivisorIntegral (-t) :=
  completedZeta_square_eq_vertical_integrals t (by norm_num : (0 : ℝ) < 1)

theorem zetaSquareContour_right_conj (t u : ℝ) :
    zetaSquareContourIntegrand (-t) (1+((-u : ℝ) : ℂ)*I) =
      conj (zetaSquareContourIntegrand t (1+(u : ℂ)*I)) := by
  have hs : afeCriticalPoint (-t)+(1+((-u : ℝ) : ℂ)*I) =
      conj (afeCriticalPoint t+(1+(u : ℂ)*I)) := by
    rw [afeCriticalPoint_neg_eq_star]
    simp
  rw [zetaSquareContourIntegrand_eq_rightKernel_mul_divisor,
    zetaSquareContourIntegrand_eq_rightKernel_mul_divisor,
    ← riemannZeta_sq_eq_divisorLSeries (by norm_num [afeCriticalPoint]),
    ← riemannZeta_sq_eq_divisorLSeries (by norm_num [afeCriticalPoint]),
    zetaSquareRightKernel_conj, hs, riemannZeta_conj]
  simp

theorem zetaSquareDivisorIntegral_conj (t : ℝ) :
    zetaSquareDivisorIntegral (-t) = conj (zetaSquareDivisorIntegral t) := by
  unfold zetaSquareDivisorIntegral zetaSquareVerticalIntegral
  simp only [Complex.ofReal_one]
  rw [← integral_neg_eq_self
    (fun u : ℝ => zetaSquareContourIntegrand (-t) (1+(u : ℂ)*I)) volume]
  simp_rw [zetaSquareContour_right_conj, integral_conj]
  simp only [map_mul, map_div₀, map_one, map_ofNat, conj_ofReal]

theorem conj_zetaSquareGammaNormalization (t : ℝ) :
    conj (zetaSquareGammaNormalization t) = zetaSquareGammaNormalization t := by
  have hs : afeCriticalPoint (-t) = conj (afeCriticalPoint t) := afeCriticalPoint_neg_eq_star t
  simp only [zetaSquareGammaNormalization, hs, gammaReal_conj, map_mul, conj_conj]
  ring

/-- The full source entry, not just its reflected branch. -/
theorem zetaSquareNorm_eq_reflected_source (t : ℝ) :
    zetaMomentCriticalNorm t ^ 2 =
      2 * (zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t).re := by
  have h : ((zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) =
      (zetaSquareDivisorIntegral t + zetaSquareDivisorIntegral (-t)) /
        zetaSquareGammaNormalization t := by
    rw [← completedZeta_square_eq_divisor_integrals, completedZeta_square_eq_norm_mul_gamma,
      mul_div_cancel_right₀ _ (zetaSquareGammaNormalization_ne_zero t)]
  have hc : zetaSquareDivisorIntegral t / zetaSquareGammaNormalization t =
      conj (zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t) := by
    rw [map_div₀, conj_zetaSquareGammaNormalization, zetaSquareDivisorIntegral_conj, conj_conj]
  rw [add_div, hc] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.add_re, Complex.conj_re, two_mul] using hr


def zetaFourthRightPiece (t : ℝ) : ℂ :=
  zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t

theorem zetaSquareNorm_eq_two_re_fourthRightPiece (t : ℝ) :
    zetaMomentCriticalNorm t^2 = 2*(zetaFourthRightPiece t).re :=
  zetaSquareNorm_eq_reflected_source t

theorem zetaFourthRightPiece_neg (t : ℝ) :
    zetaFourthRightPiece (-t) = conj (zetaFourthRightPiece t) := by
  simp only [zetaFourthRightPiece, neg_neg, zetaSquareGammaNormalization_neg,
    map_div₀, conj_zetaSquareGammaNormalization,
    zetaSquareDivisorIntegral_conj, conj_conj]

theorem zetaFourthRightPiece_re_nonneg (t : ℝ) :
    0 ≤ (zetaFourthRightPiece t).re := by
  have h := zetaSquareNorm_eq_two_re_fourthRightPiece t
  nlinarith [sq_nonneg (zetaMomentCriticalNorm t)]

theorem zeta_fourth_le_four_mul_rightPiece_sq (t : ℝ) :
    zetaMomentCriticalNorm t^4 ≤ 4*‖zetaFourthRightPiece t‖^2 := by
  have h := zetaSquareNorm_eq_two_re_fourthRightPiece t
  have hre := Complex.re_le_norm (zetaFourthRightPiece t)
  have hn := zetaFourthRightPiece_re_nonneg t
  have hs := pow_le_pow_left₀ hn hre 2
  nlinarith [sq_nonneg (zetaMomentCriticalNorm t^2 - 2*(zetaFourthRightPiece t).re)]

theorem norm_zetaSquareGammaNormalization (t : ℝ) :
    ‖zetaSquareGammaNormalization t‖ =
      ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖^2 := by
  have he : ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖ =
      ‖Complex.Gammaℝ (afeCriticalPoint t)‖ := by
    have hs : afeCriticalPoint (-t) = conj (afeCriticalPoint t) :=
      afeCriticalPoint_neg_eq_star t
    rw [hs, gammaReal_conj, Complex.norm_conj]
  rw [zetaSquareGammaNormalization, norm_mul, he, pow_two]

theorem norm_gammaSquare_div_zetaSquareGammaNormalization (t : ℝ) (w : ℂ) :
    ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t‖ =
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ := by
  rw [norm_div, norm_pow, norm_zetaSquareGammaNormalization,
    norm_pow, norm_div, div_pow]


def zetaSquarePoleShift (t : ℝ) (w : ℂ) : ℂ :=
  ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
    (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))) ^ 2

theorem criticalPoint_pole_product (t : ℝ) :
    afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  unfold afeCriticalPoint
  push_cast
  ring_nf
  simp

theorem zetaSquarePoleShift_eq_source (t : ℝ) (w : ℂ) :
    zetaSquarePoleShift t w =
      ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w))) ^ 2 /
        zetaSquarePoleNormalization t := by
  rw [← zetaSquarePoleNormalization_neg]
  exact div_pow _ _ _

theorem poleShift_sub_one_identity (t : ℝ) (w : ℂ) :
    (afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) - 1 =
      (2 * (t : ℂ) * I * w - w ^ 2) / ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  have hne : ((1 / 4 + t ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  rw [criticalPoint_pole_product]
  rw [div_sub_one hne]
  congr 1
  unfold afeCriticalPoint
  push_cast
  ring_nf
  simp

theorem norm_poleShift_linear_sub_one_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) :
    ‖(afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) - 1‖ ≤ 3 * ‖w‖ / t := by
  rw [poleShift_sub_one_identity, norm_div]
  have hn : ‖2 * (t : ℂ) * I * w - w ^ 2‖ ≤ 2 * t * ‖w‖ + ‖w‖ ^ 2 := by
    simpa only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, norm_I, mul_one] using
      norm_sub_le (2 * (t : ℂ) * I * w) (w ^ (2 : ℕ))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / 4 + t ^ 2)]
  apply (div_le_div_of_nonneg_right hn (by positivity)).trans
  apply (div_le_div_iff₀ (by positivity) ht).mpr
  have hwt : ‖w‖ * t ≤ t ^ 2 / 2 := by nlinarith
  nlinarith [norm_nonneg w,
    mul_nonneg (norm_nonneg w) (show 0 ≤ t ^ 2 - ‖w‖ * t by nlinarith)]

theorem norm_zetaSquarePoleShift_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) : ‖zetaSquarePoleShift t w‖ ≤ 9 := by
  have h := norm_poleShift_linear_sub_one_le ht hw
  have hfrac : 3 * ‖w‖ / t ≤ 3 / 2 := (div_le_iff₀ ht).mpr (by linarith)
  have hn := norm_le_norm_sub_add
    ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
      (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))) (1 : ℂ)
  simp only [norm_one] at hn
  rw [zetaSquarePoleShift, norm_pow]
  nlinarith [norm_nonneg ((afeCriticalPoint (-t) + w) *
    (1 - (afeCriticalPoint (-t) + w)) /
      (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))))]

theorem norm_zetaSquarePoleShift_sub_one_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) : ‖zetaSquarePoleShift t w - 1‖ ≤ 12 * ‖w‖ / t := by
  let p := (afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
    (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))
  have h : ‖p - 1‖ ≤ 3 * ‖w‖ / t := norm_poleShift_linear_sub_one_le ht hw
  have hfrac : 3 * ‖w‖ / t ≤ 3 / 2 := (div_le_iff₀ ht).mpr (by linarith)
  have hp : ‖p‖ ≤ 5 / 2 := by
    have hn := norm_le_norm_sub_add p (1 : ℂ)
    simp only [norm_one] at hn
    linarith
  have hpadd : ‖p + 1‖ ≤ 4 := by
    have hn := norm_add_le p (1 : ℂ)
    simp only [norm_one] at hn
    linarith
  change ‖p ^ 2 - 1‖ ≤ _
  rw [show p ^ 2 - 1 = (p - 1) * (p + 1) by ring, norm_mul]
  calc
    _ ≤ (3 * ‖w‖ / t) * 4 := mul_le_mul h hpadd (norm_nonneg _) (by positivity)
    _ = _ := by ring


def zetaFourthKernel (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100*w^2) * hughesYoungAuxiliaryZero w *
    zetaSquarePoleShift t w *
      (Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t) / w

theorem zetaFourthKernel_one (t u : ℝ) :
    zetaFourthKernel t (1+(u:ℂ)*I) =
      zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t := by
  unfold zetaFourthKernel
  rw [zetaSquarePoleShift_eq_source]
  unfold zetaSquareRightKernel
  dsimp only
  rw [zetaSquarePoleNormalization_neg]
  simp only [div_eq_mul_inv]
  ring

theorem continuous_zetaFourthKernel_vertical (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous (fun u : ℝ => zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)) := by
  have hgamma := continuous_GammaR_afe_vertical (-t) (c := c) (by linarith)
  have haux := differentiable_hughesYoungAuxiliaryZero.continuous
  have hw : ∀ u : ℝ, (c:ℂ)+(u:ℂ)*I ≠ 0 := by
    intro u hu
    have he := congrArg Complex.re hu
    norm_num at he
    linarith
  unfold zetaFourthKernel zetaSquarePoleShift
  apply Continuous.div ?_ (by fun_prop) hw
  fun_prop (disch := assumption)

theorem norm_zetaFourthKernel_vertical (t c u : ℝ) :
    ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ =
      Real.exp (100*c^2-100*u^2) *
        ‖hughesYoungAuxiliaryZero ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖zetaSquarePoleShift t ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) /
          Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ /
        ‖(c:ℂ)+(u:ℂ)*I‖ := by
  have he : (100*((c:ℂ)+(u:ℂ)*I)^2).re = 100*c^2-100*u^2 := by
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  unfold zetaFourthKernel
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_exp, he,
    norm_gammaSquare_div_zetaSquareGammaNormalization]

theorem zetaFourthRightPiece_eq_divisor_integral (t : ℝ) :
    zetaFourthRightPiece t = (1/(2*Real.pi):ℂ) *
      ∫ u : ℝ, zetaFourthKernel t (1+(u:ℂ)*I) *
        LSeries (fun n : ℕ => (n.divisors.card:ℂ))
          (afeCriticalPoint (-t)+(1+(u:ℂ)*I)) := by
  unfold zetaFourthRightPiece zetaSquareDivisorIntegral zetaSquareVerticalIntegral
  simp only [Complex.ofReal_one]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [zetaSquareContourIntegrand_eq_rightKernel_mul_divisor, zetaFourthKernel_one]
  ring



/-- The actual normalized divisor integrand is absolutely integrable, before
its integral is used to represent the right piece. -/
theorem integrable_zetaFourthKernel_mul_divisor (t : ℝ) :
    Integrable (fun u : ℝ => zetaFourthKernel t (1+(u : ℂ)*I) *
      LSeries (fun n : ℕ => (n.divisors.card : ℂ))
        (afeCriticalPoint (-t)+(1+(u : ℂ)*I))) := by
  have hi := (integrable_zetaSquareContour_vertical (-t)
    (by norm_num : (0 : ℝ) < 1)).div_const (zetaSquareGammaNormalization t)
  apply hi.congr
  filter_upwards with u
  simp only [Complex.ofReal_one]
  rw [zetaSquareContourIntegrand_eq_rightKernel_mul_divisor, zetaFourthKernel_one]
  ring

end MathCollab.Density.Stronger.Fourth
