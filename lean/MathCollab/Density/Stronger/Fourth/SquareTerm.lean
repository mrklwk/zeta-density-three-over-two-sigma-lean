module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/FOURTH_MOMENT_MANIFEST.json.
Mathlib and narrow DigammaSeries dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.SquareKernel
public import MathCollab.Density.Stronger.Fourth.SquareDivisorSeries
public import MathCollab.Density.Stronger.Fourth.Coefficients

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open MathCollab.Density.Stronger
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
def zetaFourthTerm (t : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  divisorDirichletTerm (afeCriticalPoint (-t)+w) n * zetaFourthKernel t w

theorem zetaFourthTerm_zero (t : ℝ) (w : ℂ) : zetaFourthTerm t 0 w = 0 := by
  simp [zetaFourthTerm,divisorDirichletTerm]

theorem differentiableAt_zetaFourthKernel (t : ℝ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (zetaFourthKernel t) w := by
  have hs : DifferentiableAt ℂ (fun z : ℂ => afeCriticalPoint (-t)+z) w := by fun_prop
  have hpos : 0 < (afeCriticalPoint (-t)+w).re := by
    simp [afeCriticalPoint]
    linarith
  have hgamma := (hasDerivAt_gammaReal hpos).differentiableAt.comp w hs
  have haux := differentiable_hughesYoungAuxiliaryZero.differentiableAt (x := w)
  have hw0 : w ≠ 0 := by
    intro he
    subst w
    norm_num at hw
  unfold zetaFourthKernel zetaSquarePoleShift
  fun_prop (disch := assumption)

theorem differentiableAt_zetaFourthTerm (t : ℝ) (n : ℕ)
    {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (zetaFourthTerm t n) w := by
  by_cases hn : n = 0
  · subst n
    simpa only [show zetaFourthTerm t 0 = fun _ => (0:ℂ) by
      funext z; exact zetaFourthTerm_zero t z] using
        (differentiableAt_const (0:ℂ) : DifferentiableAt ℂ (fun _ : ℂ => (0:ℂ)) w)
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have hd : DifferentiableAt ℂ
      (fun z : ℂ => divisorDirichletTerm (afeCriticalPoint (-t)+z) n) w := by
    simp only [divisorDirichletTerm_eq_divisorWeight_mul_cpow]
    fun_prop (disch := first | assumption | exact Or.inl hnC)
  exact hd.mul (differentiableAt_zetaFourthKernel t hw)

theorem norm_zetaFourthTerm_vertical (t c u : ℝ) (n : ℕ) :
    ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖ =
      ((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ := by
  rw [zetaFourthTerm,norm_mul,norm_fourth_divisorTerm_vertical]

theorem norm_fourth_divisorTerm_le_card {c : ℝ} (hc : 0 ≤ c) (t u : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖ ≤
      (n.divisors.card:ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [divisorDirichletTerm]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [norm_fourth_divisorTerm_vertical]
  exact mul_le_of_le_one_right (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))

theorem zetaFourthTerm_one (t u : ℝ) (n : ℕ) :
    zetaFourthTerm t n (1+(u:ℂ)*I) =
      zetaSquareDivisorTerm (-t) n u / zetaSquareGammaNormalization t := by
  rw [zetaFourthTerm,zetaFourthKernel_one,zetaSquareDivisorTerm]
  ring

theorem zetaFourthTerm_boundaryRect_zero
    (t : ℝ) (n : ℕ) {a b H : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(-H:ℂ)*I)) -
      (∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(H:ℂ)*I)) +
      I • (∫ y : ℝ in -H..H, zetaFourthTerm t n ((b:ℂ)+(y:ℂ)*I)) -
      I • (∫ y : ℝ in -H..H, zetaFourthTerm t n ((a:ℂ)+(y:ℂ)*I)) = 0 := by
  have hd : DifferentiableOn ℂ (zetaFourthTerm t n) ([[a,b]] ×ℂ [[-H,H]]) := by
    intro w hw
    apply (differentiableAt_zetaFourthTerm t n ?_).differentiableWithinAt
    rw [mem_reProdIm,uIcc_of_le hab] at hw
    exact ha.trans_le hw.1.1
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (zetaFourthTerm t n) ((a:ℂ)-(H:ℂ)*I) ((b:ℂ)+(H:ℂ)*I)
    (by simpa using hd)
  simpa using hrect




theorem exists_norm_zetaFourthKernel_strip_le
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) :
    ∃ K : ℝ, 0 < K ∧ ∀ c ∈ Icc a b, ∀ u : ℝ,
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤ K*Real.exp (-99*u^2) := by
  obtain ⟨G,hG,hGamma⟩ := exists_norm_GammaR_strip_le (a := 1/2+a) (b := 1/2+b) (by linarith : (0:ℝ) < 1/2+a)
  let D : ℝ := ‖(zetaSquareGammaNormalization t)⁻¹‖
  have hD : 0 < D := norm_pos_iff.mpr
    (inv_ne_zero (zetaSquareGammaNormalization_ne_zero t))
  let A : ℝ := 10000*G^2*D/a
  let Q : ℝ := 12*(3+b+t)+36
  let K : ℝ := A*Real.exp (100*b^2)*Real.exp Q
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro c hc u
  have hc0 : 0 < c := ha.trans_le hc.1
  have hb : 0 < b := ha.trans_le hab
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let R : ℝ := 3+c+t+|u|
  let B : ℝ := 3+b+t+|u|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg u]
  have hw := norm_vertical_shift_le hc0.le u
  have hwlower : a ≤ ‖w‖ := hc.1.trans (vertical_shift_re_le_norm hc0.le u)
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625*R^8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR
      (hw.trans (by dsimp [R]; linarith))
  have hpole : ‖zetaSquarePoleShift t w‖ ≤ 16*R^4 :=
    norm_zetaSquarePoleShift_le_polynomial ht hc0.le u
  have hg : ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)‖ ≤ G := by
    have heq : afeCriticalPoint (-t)+w =
        ((1/2+c:ℝ):ℂ)+((-t+u:ℝ):ℂ)*I := by
      dsimp [afeCriticalPoint,w]
      push_cast
      ring
    rw [heq]
    apply hGamma
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hgamma :
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤ G^2*D := by
    rw [← norm_gammaSquare_div_zetaSquareGammaNormalization,
      div_eq_mul_inv, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hg 2) (norm_nonneg _)
  have hRB : R ≤ B := by dsimp [R,B]; linarith [hc.2]
  have hpoly : B^12 ≤ Real.exp Q*Real.exp (u^2) := by
    have hp := abs_polynomial_mul_exp_le_gaussian
      (by positivity : 0 ≤ 3+b+t) (by norm_num : (0:ℝ) ≤ 1) 0 12 u
    norm_num at hp
    exact hp
  have hexp : Real.exp (100*c^2-100*u^2) ≤ Real.exp (100*b^2-100*u^2) := by
    apply Real.exp_le_exp.mpr
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le hc.2 2) (by norm_num)) _
  have he : Real.exp (100*b^2-100*u^2) =
      Real.exp (100*b^2)*Real.exp (-100*u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
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
    _ ≤ Real.exp (100*c^2-100*u^2)*(625*R^8)*(16*R^4)*(G^2*D)/a := by
      gcongr
    _ = A*R^12*Real.exp (100*c^2-100*u^2) := by dsimp [A]; ring
    _ ≤ A*B^12*Real.exp (100*b^2-100*u^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans (by norm_num) hR) hRB 12) hA.le)
        hexp (Real.exp_pos _).le (by positivity)
    _ = A*Real.exp (100*b^2)*B^12*Real.exp (-100*u^2) := by rw [he]; ring
    _ ≤ A*Real.exp (100*b^2)*(Real.exp Q*Real.exp (u^2))*Real.exp (-100*u^2) := by
      gcongr
    _ = K*(Real.exp (u^2)*Real.exp (-100*u^2)) := by dsimp [K]; ring
    _ = _ := by rw [hgauss]




theorem continuous_zetaFourthTerm_vertical (t : ℝ) (n : ℕ)
    {c : ℝ} (hc : 0 < c) :
    Continuous (fun u : ℝ => zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hw : 0 < ((c:ℂ)+(u:ℂ)*I).re := by simpa using hc
  have hline : ContinuousAt (fun v : ℝ => (c:ℂ)+(v:ℂ)*I) u := by fun_prop
  exact (differentiableAt_zetaFourthTerm t n hw).continuousAt.comp
    (f := fun v : ℝ => (c:ℂ)+(v:ℂ)*I) hline

theorem exists_norm_zetaFourthTerm_strip_le
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Icc a b, ∀ u : ℝ,
      ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖ ≤ C*Real.exp (-99*u^2) := by
  obtain ⟨K,hK,hbound⟩ := exists_norm_zetaFourthKernel_strip_le ha hab ht
  refine ⟨K*((n.divisors.card:ℝ)+1),by positivity,?_⟩
  intro c hc u
  have hD := norm_fourth_divisorTerm_le_card (ha.le.trans hc.1) t u n
  rw [zetaFourthTerm,norm_mul]
  calc
    _ ≤ (n.divisors.card:ℝ)*(K*Real.exp (-99*u^2)) :=
      mul_le_mul hD (hbound c hc u) (norm_nonneg _) (by positivity)
    _ ≤ K*((n.divisors.card:ℝ)+1)*Real.exp (-99*u^2) := by
      nlinarith [mul_nonneg hK.le (Real.exp_pos (-99*u^2)).le]

theorem integrable_zetaFourthTerm_vertical {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 < c) (n : ℕ) :
    Integrable (fun u : ℝ => zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)) := by
  obtain ⟨K,_,hK⟩ := exists_norm_zetaFourthTerm_strip_le hc le_rfl ht n
  have hg : Integrable (fun u : ℝ => K*Real.exp (-99*u^2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 99)).const_mul K
  exact hg.mono' (continuous_zetaFourthTerm_vertical t n hc).aestronglyMeasurable
    (Eventually.of_forall (fun u => hK c ⟨le_rfl,le_rfl⟩ u))

theorem tendsto_zetaFourthTerm_horizontal_of_sq_eq
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ)
    (v : ℝ → ℝ) (hv : ∀ H : ℝ, (v H)^2 = H^2) :
    Tendsto (fun H : ℝ =>
      ∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(v H:ℂ)*I)) atTop (𝓝 0) := by
  obtain ⟨K,_,hK⟩ := exists_norm_zetaFourthTerm_strip_le ha hab ht n
  have hbnd : ∀ H : ℝ,
      ‖∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(v H:ℂ)*I)‖ ≤
        (K*Real.exp (-99*H^2))*|b-a| := by
    intro H
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Icc a b := by
      rw [← uIcc_of_le hab]
      exact uIoc_subset_uIcc hx
    simpa only [hv H] using hK x hx' (v H)
  have hp : Tendsto (fun H : ℝ => H^2) atTop atTop :=
    tendsto_pow_atTop (by decide : 2 ≠ 0)
  have hm : Tendsto (fun H : ℝ => 99*H^2) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 99) hp
  have he : Tendsto (fun H : ℝ => Real.exp (-99*H^2)) atTop (𝓝 0) := by
    simpa only [neg_mul] using! Real.tendsto_exp_neg_atTop_nhds_zero.comp hm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hbnd
  simpa using (he.const_mul K).mul_const |b-a|





end MathCollab.Density.Stronger.Fourth
