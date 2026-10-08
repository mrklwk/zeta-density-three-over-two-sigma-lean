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
public import MathCollab.Density.Stronger.Fourth.SquareSource
public import MathCollab.Density.AbelZetaGrowth
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger.Fourth MathCollab.Density.ZetaGrowth
open MathCollab.Density.Contour
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem norm_Gamma_le_realGamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  calc
    ‖∫ x in Set.Ioi (0 : ℝ),
        ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Set.Ioi (0 : ℝ),
          ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-x) * x ^ (s.re - 1) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.sub_re, Complex.one_re]
      simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Height-uniform majorant for Deligne's real Gamma factor on a positive
vertical line. -/
theorem norm_GammaR_le_realGamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤
      Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hreHalf : (s / 2).re = s.re / 2 := by
    norm_num [Complex.div_re, Complex.normSq]
  have hhalf : 0 < (s / 2).re := by
    rw [hreHalf]
    linarith
  have hGamma := norm_Gamma_le_realGamma_re hhalf
  have hre : (-s / 2).re = -s.re / 2 := by
    norm_num [Complex.div_re, Complex.normSq]
  rw [hre]
  rw [hreHalf] at hGamma
  exact mul_le_mul_of_nonneg_left hGamma (by positivity)

/-- GammaR is uniformly bounded on every compact positive real-part strip. -/
theorem exists_norm_GammaR_strip_le {a b : ℝ} (ha : 0 < a) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, s.re ∈ Icc a b → ‖Gammaℝ s‖ ≤ G := by
  let major : ℝ → ℝ := fun x => Real.pi ^ (-x/2) * Real.Gamma (x/2)
  have hgamma : ContinuousOn (fun x : ℝ => Real.Gamma (x/2)) (Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop)
      (fun x hx => by change 0 < x/2; linarith [hx.1])
  have hpow : Continuous (fun x : ℝ => Real.pi ^ (-x/2)) :=
    (Real.continuous_const_rpow Real.pi_ne_zero).comp (by fun_prop)
  have hcont : ContinuousOn major (Icc a b) := hpow.continuousOn.mul hgamma
  obtain ⟨G, hG⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max 1 G, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro s hs
  exact (norm_GammaR_le_realGamma_re (ha.trans_le hs.1)).trans
    ((hG ⟨s.re, hs, rfl⟩).trans (le_max_right _ _))

/-- Cubic growth on a compact right strip, away from the real-axis poles. -/
theorem norm_completedXiNumerator_right_strip_le {c G : ℝ}
    (_hG : 0 < G)
    (hgamma : ∀ s : ℂ, s.re ∈ Icc (1/2) (1/2+c) → ‖Gammaℝ s‖ ≤ G)
    {s : ℂ} (hre : s.re ∈ Icc (1/2) (1/2+c)) (him : 1 ≤ |s.im|) :
    ‖completedXiNumerator s‖ ≤ 5*G*(1+‖s‖)^3 := by
  have hs0 : s ≠ 0 := by
    intro hs; subst s; norm_num at hre
  have hs1 : s ≠ 1 := by
    intro hs; subst s; norm_num at him
  have hsre : 0 < s.re := by linarith [hre.1]
  have hz := norm_riemannZeta_le_five_mul_norm (s := s) (by linarith [hre.1]) him
  have hg := hgamma s hre
  have hn : ‖s‖ ≤ 1+‖s‖ := by linarith
  have hm : ‖1-s‖ ≤ 1+‖s‖ := by simpa using norm_sub_le (1 : ℂ) s
  rw [completedXiNumerator_eq s hs0 hs1, completedRiemannZeta_eq_zeta_mul_GammaR hsre,
    norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ (1+‖s‖)*(1+‖s‖)*((5*(1+‖s‖))*G) := by gcongr; linarith
    _ = _ := by ring

/-- Functional-equation reflection gives cubic growth on a strip centered at 1/2. -/
theorem exists_completedXiNumerator_strip_cubic_high {c : ℝ} (_hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re-1/2| ≤ c → 1 ≤ |s.im| →
      ‖completedXiNumerator s‖ ≤ C*(1+‖s‖)^3 := by
  obtain ⟨G, hG, hgamma⟩ := exists_norm_GammaR_strip_le
    (a := 1/2) (b := 1/2+c) (by norm_num)
  refine ⟨40*G, by positivity, ?_⟩
  intro s hre him
  have hre' := abs_le.mp hre
  by_cases hs : 1/2 ≤ s.re
  · have h := norm_completedXiNumerator_right_strip_le hG hgamma
      (s := s) ⟨hs, by linarith [hre'.2]⟩ him
    exact h.trans (by gcongr; linarith)
  · have hw : (1-s).re ∈ Icc (1/2) (1/2+c) := by
      simp only [sub_re, one_re]; constructor <;> linarith [hre'.1]
    have him' : 1 ≤ |(1-s).im| := by simpa using him
    have h := norm_completedXiNumerator_right_strip_le hG hgamma hw him'
    rw [completedXiNumerator_one_sub] at h
    have hn : 1+‖1-s‖ ≤ 2*(1+‖s‖) := by
      have hm := norm_sub_le (1 : ℂ) s
      norm_num at hm
      linarith [norm_nonneg s]
    calc
      _ ≤ 5*G*(1+‖1-s‖)^3 := h
      _ ≤ 5*G*(2*(1+‖s‖))^3 := by gcongr
      _ = _ := by ring


/-- The compact middle of the strip supplies the same cubic bound at every height. -/
theorem exists_completedXiNumerator_strip_cubic {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re-1/2| ≤ c →
      ‖completedXiNumerator s‖ ≤ C*(1+‖s‖)^3 := by
  obtain ⟨C, hC, hhigh⟩ := exists_completedXiNumerator_strip_cubic_high hc
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : ℂ) (c+2)).bddAbove_image
    (differentiable_completedXiNumerator.continuous.norm.continuousOn)
  refine ⟨max C D, lt_max_of_lt_left hC, ?_⟩
  intro s hs
  by_cases him : 1 ≤ |s.im|
  · exact (hhigh s hs him).trans (by gcongr; exact le_max_left _ _)
  · have hre := abs_le.mp hs
    have habs : |s.re| ≤ c+1/2 := abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩
    have hn : ‖s‖ ≤ c+2 := (Complex.norm_le_abs_re_add_abs_im s).trans (by linarith)
    have hball : s ∈ Metric.closedBall (0 : ℂ) (c+2) := by simpa using hn
    have hb : ‖completedXiNumerator s‖ ≤ D := hD ⟨s, hball, rfl⟩
    have hp : 1 ≤ (1+‖s‖)^3 := one_le_pow₀ (by linarith [norm_nonneg s])
    exact hb.trans ((le_max_right C D).trans (le_mul_of_one_le_right
      (le_trans hC.le (le_max_left _ _)) hp))

end MathCollab.Density.Stronger.Fourth
