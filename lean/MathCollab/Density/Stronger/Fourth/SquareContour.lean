module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
The fixed-strip growth and Gaussian contour majorants are new proofs.
See ../../../../../third_party/twelfth/SQUARE_GROWTH_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
No global-order, Hadamard, Architect, or upstream project module is imported.
-/
public import MathCollab.Density.Stronger.Fourth.SquareGrowth
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem norm_hughesYoungAuxiliaryZero_le_polynomial
    {w : ℂ} {R : ℝ} (hR : 1 ≤ R) (hw : ‖w‖ ≤ R) :
    ‖hughesYoungAuxiliaryZero w‖ ≤ 625 * R ^ 8 := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hsq : ‖w‖ ^ 2 ≤ R ^ 2 := by nlinarith
  have hbase : ‖1 - 4 * w ^ 2‖ ≤ 1 + 4 * R ^ 2 := by
    calc
      ‖1 - 4 * w ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖4 * w ^ 2‖ := norm_sub_le _ _
      _ = 1 + 4 * ‖w‖ ^ 2 := by simp [norm_pow]
      _ ≤ 1 + 4 * R ^ 2 := by nlinarith
  have hbaseCoarse : 1 + 4 * R ^ 2 ≤ 5 * R ^ 2 := by
    nlinarith [sq_nonneg R]
  unfold hughesYoungAuxiliaryZero
  rw [norm_pow]
  calc
    ‖1 - 4 * w ^ 2‖ ^ 4 ≤ (1 + 4 * R ^ 2) ^ 4 := by gcongr
    _ ≤ (5 * R ^ 2) ^ 4 := by gcongr
    _ = 625 * R ^ 8 := by ring


def gaussianPolynomial (u : ℝ) : ℝ := (1+|u|)^14 * Real.exp (-100*u^2)

theorem gaussianPolynomial_nonneg (u : ℝ) : 0 ≤ gaussianPolynomial u := by
  unfold gaussianPolynomial
  positivity

/-- Uniform in the real coordinate on each fixed strip. -/
theorem exists_zetaSquareNumerator_strip_gaussian (t c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ x u : ℝ, |x| ≤ c →
      ‖zetaSquareContourNumerator t ((x : ℂ)+(u : ℂ)*I)‖ ≤ K*gaussianPolynomial u := by
  obtain ⟨C,hC,hxi⟩ := exists_completedXiNumerator_strip_cubic hc
  let A : ℝ := 2+|t|+c
  have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg t]
  have hp : 0 < ‖zetaSquarePoleNormalization t‖ :=
    norm_pos_iff.mpr (zetaSquarePoleNormalization_ne_zero t)
  refine ⟨Real.exp (100*c^2)*625*C^2*A^14/‖zetaSquarePoleNormalization t‖,
    by positivity, ?_⟩
  intro x u hx
  let w : ℂ := (x : ℂ)+(u : ℂ)*I
  let R : ℝ := A*(1+|u|)
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le hA (by linarith [abs_nonneg u])
  have hwn : ‖w‖ ≤ R := by
    have hn : ‖w‖ ≤ |x|+|u| := by
      simpa [w] using Complex.norm_le_abs_re_add_abs_im w
    have hAc : c ≤ A := by dsimp [A]; linarith [abs_nonneg t]
    dsimp [R]
    nlinarith [abs_nonneg u]
  have hsn : 1+‖afeCriticalPoint t+w‖ ≤ R := by
    have hn : ‖afeCriticalPoint t+w‖ ≤ |1/2+x|+|t+u| := by
      simpa [afeCriticalPoint,w] using Complex.norm_le_abs_re_add_abs_im (afeCriticalPoint t+w)
    have hreal : |1/2+x| ≤ 1/2+|x| := by
      simpa using abs_add_le (1/2 : ℝ) x
    have him := abs_add_le t u
    dsimp [R,A]
    nlinarith [abs_nonneg t, abs_nonneg u]
  have hstrip : |(afeCriticalPoint t+w).re-1/2| ≤ c := by simpa [afeCriticalPoint,w] using hx
  have hxi' : ‖completedXiNumerator (afeCriticalPoint t+w)‖ ≤ C*R^3 :=
    (hxi _ hstrip).trans (by gcongr)
  have haux := norm_hughesYoungAuxiliaryZero_le_polynomial hR hwn
  have hgauss : ‖Complex.exp (100*w^2)‖ ≤ Real.exp (100*c^2)*Real.exp (-100*u^2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hxsq : x^2 ≤ c^2 := by
      have h := mul_self_le_mul_self (abs_nonneg x) hx
      simpa [← pow_two] using h
    norm_num [w,pow_two,mul_re,mul_im]
    nlinarith only [hxsq]
  unfold zetaSquareContourNumerator
  change ‖Complex.exp (100*w^2)*hughesYoungAuxiliaryZero w*
    completedXiNumerator (afeCriticalPoint t+w)^2/zetaSquarePoleNormalization t‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (Real.exp (100*c^2)*Real.exp (-100*u^2))*(625*R^8)*(C*R^3)^2 /
        ‖zetaSquarePoleNormalization t‖ := by gcongr
    _ = _ := by
      have hfactor (e f k a v p : ℝ) :
          (e*f)*(625*(a*v)^8)*(k*(a*v)^3)^2/p =
            (e*625*k^2*a^14/p)*(v^14*f) := by ring
      exact hfactor _ _ _ _ _ _

/-- Continuity on every nonzero vertical line. -/
theorem continuous_zetaSquareContour_vertical (t : ℝ) {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun u : ℝ => zetaSquareContourIntegrand t ((c : ℂ)+(u : ℂ)*I)) := by
  have hw : Continuous (fun u : ℝ => (c : ℂ)+(u : ℂ)*I) := by fun_prop
  have hnum := (differentiable_zetaSquareContourNumerator t).continuous.comp hw
  apply hnum.div hw
  intro u he
  have hre := congrArg Complex.re he
  simp at hre
  exact hc hre


theorem gaussianPolynomial_le (u : ℝ) :
    gaussianPolynomial u ≤ 2^14*(Real.exp (-100*u^2)+u^14*Real.exp (-100*u^2)) := by
  have hpoly : (1+|u|)^14 ≤ (2 : ℝ)^14*(1+u^14) := by
    have heven : |u|^14 = u^14 := (by decide : Even (14 : ℕ)).pow_abs u
    have hpow0 : 0 ≤ u^14 := by rw [← heven]; positivity
    by_cases hu : |u| ≤ 1
    · calc
        _ ≤ (2 : ℝ)^14 := by gcongr; linarith [abs_nonneg u]
        _ ≤ _ := by nlinarith
    · calc
        _ ≤ (2*|u|)^14 := by gcongr; linarith
        _ = (2 : ℝ)^14*u^14 := by rw [mul_pow, heven]
        _ ≤ _ := by nlinarith
  unfold gaussianPolynomial
  calc
    _ ≤ ((2 : ℝ)^14*(1+u^14))*Real.exp (-100*u^2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = _ := by ring

theorem integrable_gaussianPolynomial : Integrable gaussianPolynomial := by
  have h0 := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 100)
  have h14 : Integrable (fun u : ℝ => u^14*Real.exp (-100*u^2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 100)
        (by norm_num : (-1 : ℝ) < (14 : ℕ))
  have hmajor := (h0.add h14).const_mul ((2 : ℝ)^14)
  apply hmajor.mono' (by unfold gaussianPolynomial; fun_prop)
  filter_upwards with u
  rw [Real.norm_of_nonneg (gaussianPolynomial_nonneg u)]
  exact gaussianPolynomial_le u

theorem tendsto_gaussianPolynomial_zero : Tendsto gaussianPolynomial atTop (𝓝 0) := by
  have hbase : Tendsto (fun u : ℝ => Real.exp (-(1/2 : ℝ)*u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1/2 : ℝ) < 0))
  have h0 : Tendsto (fun u : ℝ => Real.exp (-100*u^2)) atTop (𝓝 0) := by
    simpa using (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 100) 0).tendsto_zero_of_tendsto hbase
  have h14 : Tendsto (fun u : ℝ => u^14*Real.exp (-100*u^2)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 100) (14 : ℕ)).tendsto_zero_of_tendsto hbase
  apply squeeze_zero (fun u => gaussianPolynomial_nonneg u) gaussianPolynomial_le
  simpa using (h0.add h14).const_mul ((2 : ℝ)^14)


theorem norm_zetaSquareContour_le_of_lower
    {t x u K d : ℝ} (hK : 0 ≤ K) (hd : 0 < d)
    (hnum : ‖zetaSquareContourNumerator t ((x : ℂ)+(u : ℂ)*I)‖ ≤ K*gaussianPolynomial u)
    (hden : d ≤ ‖(x : ℂ)+(u : ℂ)*I‖) :
    ‖zetaSquareContourIntegrand t ((x : ℂ)+(u : ℂ)*I)‖ ≤ (K/d)*gaussianPolynomial u := by
  rw [zetaSquareContourIntegrand, norm_div]
  calc
    _ ≤ (K*gaussianPolynomial u)/‖(x : ℂ)+(u : ℂ)*I‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (K*gaussianPolynomial u)/d := div_le_div_of_nonneg_left
      (mul_nonneg hK (gaussianPolynomial_nonneg u)) hd hden
    _ = _ := by ring

/-- Absolute integrability of the full actual-zeta contour on any positive vertical line. -/
theorem integrable_zetaSquareContour_vertical (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => zetaSquareContourIntegrand t ((c : ℂ)+(u : ℂ)*I)) := by
  obtain ⟨K,hK,hbound⟩ := exists_zetaSquareNumerator_strip_gaussian t c hc.le
  apply (integrable_gaussianPolynomial.const_mul (K/c)).mono'
    (continuous_zetaSquareContour_vertical t hc.ne').aestronglyMeasurable
  filter_upwards with u
  apply norm_zetaSquareContour_le_of_lower hK.le hc
    (hbound c u (by rw [abs_of_pos hc]))
  have h := Complex.abs_re_le_norm ((c : ℂ)+(u : ℂ)*I)
  simpa [abs_of_pos hc] using h

/-- Both sides of the symmetric rectangle have a uniform decaying horizontal majorant. -/
theorem tendsto_hIntegral_zetaSquare_top_zero (t c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ => HIntegral (zetaSquareContourIntegrand t) (-c) c H)
      atTop (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := exists_zetaSquareNumerator_strip_gaussian t c hc
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (zetaSquareContourIntegrand t) (-c) c H‖ ≤
        (K*gaussianPolynomial H)*|c-(-c)| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Icc (-c) c := by
        have h := Set.uIoc_subset_uIcc hx
        rwa [uIcc_of_le (by linarith : -c ≤ c)] at h
      have hden : 1 ≤ ‖(x : ℂ)+(H : ℂ)*I‖ := by
        have h := Complex.abs_im_le_norm ((x : ℂ)+(H : ℂ)*I)
        have hH0 : 0 ≤ H := by linarith
        simpa [abs_of_nonneg hH0] using hH.trans (by simpa [abs_of_nonneg hH0] using h)
      simpa using norm_zetaSquareContour_le_of_lower hK.le zero_lt_one
        (hbound x H (abs_le.mpr hx')) hden)
  simpa using (tendsto_gaussianPolynomial_zero.const_mul K).mul_const |c-(-c)|

theorem tendsto_hIntegral'_zetaSquare_top_zero (t c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ => HIntegral' (zetaSquareContourIntegrand t) (-c) c H)
      atTop (𝓝 0) := by
  unfold HIntegral'
  simpa using (tendsto_hIntegral_zetaSquare_top_zero t c hc).const_smul
    (1/(2*Real.pi*I))

/-- The reflected vertical contours converge to the literal completed zeta square. -/
theorem zetaSquareAFE_vertical_limit (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ =>
      VIntegral' (zetaSquareContourIntegrand t) c (-H) H +
      VIntegral' (zetaSquareContourIntegrand (-t)) c (-H) H)
      atTop (𝓝 (completedRiemannZeta (afeCriticalPoint t)^2)) := by
  let F : ℂ := completedRiemannZeta (afeCriticalPoint t)^2
  have ht := tendsto_hIntegral'_zetaSquare_top_zero t c hc.le
  have hmt := tendsto_hIntegral'_zetaSquare_top_zero (-t) c hc.le
  have htarget : Tendsto (fun H : ℝ => F +
      HIntegral' (zetaSquareContourIntegrand t) (-c) c H +
      HIntegral' (zetaSquareContourIntegrand (-t)) (-c) c H)
      atTop (𝓝 F) := by
    simpa using (tendsto_const_nhds.add ht).add hmt
  apply htarget.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have hfinite := zetaSquareAFE_truncated_native t hc hH
  change F = _ at hfinite
  linear_combination hfinite

def zetaSquareVerticalIntegral (t c : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ u : ℝ, zetaSquareContourIntegrand t ((c : ℂ)+(u : ℂ)*I)

theorem tendsto_zetaSquare_vertical_integral (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => VIntegral' (zetaSquareContourIntegrand t) c (-H) H)
      atTop (𝓝 (zetaSquareVerticalIntegral t c)) := by
  unfold zetaSquareVerticalIntegral
  have h := (intervalIntegral_tendsto_integral (integrable_zetaSquareContour_vertical t hc)
    tendsto_neg_atTop_atBot tendsto_id).const_mul (1/(2*Real.pi) : ℂ)
  convert h using 1
  funext H
  unfold VIntegral' VIntegral
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  rfl

/-- Exact infinite-height actual-zeta identity; no contour limit is assumed. -/
theorem completedZeta_square_eq_vertical_integrals (t : ℝ) {c : ℝ} (hc : 0 < c) :
    completedRiemannZeta (afeCriticalPoint t)^2 =
      zetaSquareVerticalIntegral t c + zetaSquareVerticalIntegral (-t) c := by
  exact tendsto_nhds_unique (zetaSquareAFE_vertical_limit t hc)
    ((tendsto_zetaSquare_vertical_integral t hc).add
      (tendsto_zetaSquare_vertical_integral (-t) hc))

theorem zetaSquareNorm_eq_vertical_integrals (t : ℝ) {c : ℝ} (hc : 0 < c) :
    MathCollab.Density.Stronger.zetaMomentCriticalNorm t^2 =
      ((zetaSquareVerticalIntegral t c + zetaSquareVerticalIntegral (-t) c)/
        zetaSquareGammaNormalization t).re := by
  rw [← completedZeta_square_eq_vertical_integrals t hc,
    completedZeta_square_eq_norm_mul_gamma,
    mul_div_cancel_right₀ _ (zetaSquareGammaNormalization_ne_zero t), Complex.ofReal_re]

end MathCollab.Density.Stronger.Fourth
