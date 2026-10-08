module
-- Reversible module-visibility port of the audited development.
/-
Selected exponential-tail truncation and compact-height extension proofs
adapted from Scott McColm, PointMeanLemmaThreeTail.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
This module proves the literal point-mean proposition from the native
Gamma-zeta-square contour chain; no moment bound is assumed.
-/
public import MathCollab.Density.Stronger.PointMean.VerticalEdges
public import MathCollab.Density.Stronger.PointMean.Statement

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.ZetaGrowth
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The critical-line zeta norm has a global quadratic majorant.  The compact
part is supplied by continuity; outside it the elementary vertical zeta bound
is sufficient. -/
theorem exists_zetaMomentCriticalNorm_sq_le_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ C * (1 + y ^ (2 : ℕ)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (continuous_zetaMomentCriticalNorm.pow 2).continuousOn
  let C : ℝ := max 100 B
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_left 100 B), ?_⟩
  intro y
  by_cases hy : |y| ≤ 1
  · have hyMem : y ∈ Set.Icc (-1 : ℝ) 1 := by
      exact (abs_le.mp hy)
    have hyB : zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ B :=
      hB ⟨y, hyMem, rfl⟩
    have hBC : B ≤ C := le_max_right 100 B
    have hC : 0 ≤ C := (lt_of_lt_of_le (by norm_num) (le_max_left 100 B)).le
    calc
      zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ C := hyB.trans hBC
      _ = C * 1 := by ring
      _ ≤ C * (1 + y ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg y]) hC
  · have hyOne : 1 < |y| := lt_of_not_ge hy
    let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I
    have hzRe : (1 / 4 : ℝ) ≤ z.re := by
      simp [z]
      norm_num
    have hzeta := norm_riemannZeta_le_five_mul_norm hzRe
      (by simpa [z] using hyOne.le)
    have hnorm : ‖z‖ ≤ 2 * |y| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (1 / 2 : ℝ) + |y| := by simp [z]
        _ ≤ 2 * |y| := by linarith
    have hzeta' : zetaMomentCriticalNorm y ≤ 10 * |y| := by
      unfold zetaMomentCriticalNorm
      change ‖riemannZeta z‖ ≤ _
      exact hzeta.trans (by nlinarith)
    have hsq : zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ 100 * y ^ (2 : ℕ) := by
      calc
        zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ (10 * |y|) ^ (2 : ℕ) :=
          pow_le_pow_left₀
            (norm_nonneg (riemannZeta
              (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) hzeta' 2
        _ = 100 * y ^ (2 : ℕ) := by
          rw [mul_pow, sq_abs]
          norm_num
    have hC100 : (100 : ℝ) ≤ C := le_max_left 100 B
    have hC : 0 ≤ C := by linarith
    calc
      zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ 100 * y ^ (2 : ℕ) := hsq
      _ ≤ C * y ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hC100 (sq_nonneg y)
      _ ≤ C * (1 + y ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hC

theorem integral_exp_neg_half_abs_heathBrown :
    (∫ x : ℝ, Real.exp (-|x| / 2)) = 4 := by
  have hchange := Measure.integral_comp_mul_left
    (fun y : ℝ => Real.exp (-|y|)) (1 / 2 : ℝ)
  have hrewrite : (fun x : ℝ => Real.exp (-|x| / 2)) =
      fun x : ℝ => Real.exp (-|(1 / 2 : ℝ) * x|) := by
    funext x
    congr 1
    rw [abs_mul]
    norm_num
    ring
  rw [hrewrite, hchange, integral_exp_neg_abs_heathBrown]
  norm_num

theorem integrable_exp_neg_half_abs_heathBrown :
    Integrable (fun x : ℝ => Real.exp (-|x| / 2)) := by
  have h := integrable_exp_neg_abs_heathBrown.comp_mul_left'
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  convert h using 1
  funext x
  rw [abs_mul]
  norm_num
  ring

/-- Beyond the source radius `(log t)^2`, the polynomial vertical growth of
zeta is swallowed by half of the exponential kernel. -/
theorem heathBrown_fullMoment_tail_pointwise
    {C t u : ℝ}
    (hC : ∀ y : ℝ,
      zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ C * (1 + y ^ (2 : ℕ)))
    (ht : 10 ≤ t) (hlog : 4 ≤ Real.log t)
    (hu : Real.log t ^ (2 : ℕ) ≤ |u|) :
    Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
      (19 * C) * Real.exp (-|u| / 2) := by
  have htPos : 0 < t := by linarith
  have hlogNonneg : 0 ≤ Real.log t := by linarith
  have habsNonneg : 0 ≤ |u| := abs_nonneg u
  have htExp : t ^ (2 : ℕ) ≤ Real.exp (|u| / 2) := by
    have hExponent : 2 * Real.log t ≤ |u| / 2 := by
      nlinarith [sq_nonneg (Real.log t - 4)]
    calc
      t ^ (2 : ℕ) = Real.exp (Real.log t) ^ (2 : ℕ) := by
        rw [Real.exp_log htPos]
      _ = Real.exp (2 * Real.log t) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ Real.exp (|u| / 2) := Real.exp_le_exp.mpr hExponent
  have huExp : u ^ (2 : ℕ) ≤ 8 * Real.exp (|u| / 2) := by
    have hp := Real.pow_div_factorial_le_exp
      (x := |u| / 2) (by positivity) 2
    norm_num at hp ⊢
    nlinarith [sq_abs u]
  have hOneExp : 1 ≤ Real.exp (|u| / 2) := by
    rw [Real.one_le_exp_iff]
    positivity
  have hquad : 1 + (t + u) ^ (2 : ℕ) ≤
      19 * Real.exp (|u| / 2) := by
    have hadd : (t + u) ^ (2 : ℕ) ≤
        2 * t ^ (2 : ℕ) + 2 * u ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (t - u)]
    nlinarith
  have hzeta := hC (t + u)
  have hCnonneg : 0 ≤ C := by
    have hz0 := hC 0
    simpa using (le_trans (sq_nonneg (zetaMomentCriticalNorm 0)) hz0)
  calc
    Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
        Real.exp (-|u|) * (C * (1 + (t + u) ^ (2 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left hzeta (Real.exp_pos _).le
    _ ≤ Real.exp (-|u|) * (C * (19 * Real.exp (|u| / 2))) := by
      gcongr
    _ = (19 * C) * Real.exp (-|u| / 2) := by
      calc
        Real.exp (-|u|) * (C * (19 * Real.exp (|u| / 2))) =
            (19 * C) * (Real.exp (-|u|) * Real.exp (|u| / 2)) := by ring
        _ = (19 * C) * Real.exp (-|u| / 2) := by
          rw [← Real.exp_add]
          congr 2
          ring

/-- Exact quantitative removal of the complete exponential tail at the
radius used in Heath--Brown's printed Lemma 3. -/
theorem exists_heathBrownFullCriticalMoment_le_truncated :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 10 ≤ t → 4 ≤ Real.log t →
      heathBrownFullCriticalMoment t ≤
        heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)) + D := by
  obtain ⟨C, hCpos, hC⟩ := exists_zetaMomentCriticalNorm_sq_le_quadratic
  let D : ℝ := 4 * (19 * C)
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro t ht hlog
  let H : ℝ := Real.log t ^ (2 : ℕ)
  let f : ℝ → ℝ := fun u =>
    Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)
  let g : ℝ → ℝ := fun u => (19 * C) * Real.exp (-|u| / 2)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hf : Integrable f := by
    simpa only [f] using integrable_heathBrownFullCriticalMoment t
  have hg : Integrable g :=
    integrable_exp_neg_half_abs_heathBrown.const_mul (19 * C)
  have htail : ∀ u ∈ (Set.Ioc (-H) H)ᶜ, f u ≤ g u := by
    intro u hu
    have huCases : u ≤ -H ∨ H < u := by
      simpa only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le]
        using hu
    have huAbs : H ≤ |u| := by
      rcases huCases with huLeft | huRight
      · have huNonpos : u ≤ 0 := by linarith
        rw [abs_of_nonpos huNonpos]
        linarith
      · have huPos : 0 < u := lt_of_le_of_lt hH huRight
        rw [abs_of_pos huPos]
        exact huRight.le
    dsimp only [f, g]
    exact heathBrown_fullMoment_tail_pointwise hC ht hlog
      (by simpa only [H] using huAbs)
  have htailIntegral :
      (∫ u in (Set.Ioc (-H) H)ᶜ, f u) ≤ D := by
    calc
      (∫ u in (Set.Ioc (-H) H)ᶜ, f u) ≤
          ∫ u in (Set.Ioc (-H) H)ᶜ, g u := by
        exact MeasureTheory.setIntegral_mono_on hf.integrableOn hg.integrableOn
          measurableSet_Ioc.compl htail
      _ ≤ ∫ u : ℝ, g u := by
        exact MeasureTheory.setIntegral_le_integral hg
          (Filter.Eventually.of_forall fun u => by dsimp only [g]; positivity)
      _ = D := by
        dsimp only [g, D]
        rw [integral_const_mul, integral_exp_neg_half_abs_heathBrown]
        ring
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Ioc (-H) H) measurableSet_Ioc hf
  unfold heathBrownFullCriticalMoment heathBrownLemmaThreeMoment
  change (∫ u : ℝ, f u) ≤ (∫ u in -H..H, f u) + D
  rw [intervalIntegral.integral_of_le (by linarith)]
  rw [← hsplit]
  exact add_le_add_right htailIntegral _

theorem heathBrownLemmaThreeMoment_nonneg
    {t L : ℝ} (hL : 0 ≤ L) :
    0 ≤ heathBrownLemmaThreeMoment t L := by
  unfold heathBrownLemmaThreeMoment
  exact intervalIntegral.integral_nonneg (by linarith) fun u hu => by positivity

/-- The contour estimate after replacing the complete convolution by the
literal truncated moment in the source statement. -/
theorem exists_eventually_heathBrownLemmaThree_truncated :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t *
          (1 + heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ))) := by
  obtain ⟨C₀, hC₀pos, hFull⟩ :=
    exists_eventually_heathBrownLemmaThree_fullMoment
  obtain ⟨D, hDpos, hTail⟩ :=
    exists_heathBrownFullCriticalMoment_le_truncated
  let C : ℝ := C₀ * (1 + D)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  have hLogEventually : ∀ᶠ t : ℝ in atTop, 4 ≤ Real.log t :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 4)
  filter_upwards [hFull, eventually_ge_atTop (10 : ℝ), hLogEventually]
    with t hFullT ht hlog
  let M : ℝ := heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ))
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact heathBrownLemmaThreeMoment_nonneg (by positivity)
  have hTailT : heathBrownFullCriticalMoment t ≤ M + D := by
    simpa only [M] using hTail t ht hlog
  have hlogNonneg : 0 ≤ Real.log t := by linarith
  have hFactor : 1 + heathBrownFullCriticalMoment t ≤ (1 + D) * (1 + M) := by
    have hDM : 0 ≤ D * M := mul_nonneg hDpos.le hM
    nlinarith
  calc
    zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C₀ * Real.log t * (1 + heathBrownFullCriticalMoment t) := hFullT
    _ ≤ C₀ * Real.log t * ((1 + D) * (1 + M)) := by
      exact mul_le_mul_of_nonneg_left hFactor (mul_nonneg hC₀pos.le hlogNonneg)
    _ = C * Real.log t * (1 + M) := by
      dsimp only [C]
      ring

/-- Heath--Brown (1978), Lemma 3, proved with its literal truncated
exponential moment and an absolute constant valid on the whole source range
`t ≥ 10`. -/
theorem heathBrownLemmaThree_native : HeathBrownLemmaThree := by
  obtain ⟨C₀, hC₀pos, hEventually⟩ :=
    exists_eventually_heathBrownLemmaThree_truncated
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hEventually
  let K : ℝ := max 10 T₀
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (K := Set.Icc (10 : ℝ) K)
    (continuous_zetaMomentCriticalNorm.pow 2).continuousOn
  let C : ℝ := max C₀ (max 1 B)
  have hCpos : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one
      ((le_max_left 1 B).trans (le_max_right C₀ (max 1 B)))
  refine ⟨C, hCpos, ?_⟩
  intro t ht
  let M : ℝ := heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ))
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact heathBrownLemmaThreeMoment_nonneg (by positivity)
  have hlogTwo : 2 < Real.log t := two_lt_log_of_ten_le ht
  have hlogNonneg : 0 ≤ Real.log t := by linarith
  have hOneM : 0 ≤ 1 + M := by linarith
  by_cases hlarge : T₀ ≤ t
  · have hSource := hT₀ t hlarge
    have hC₀C : C₀ ≤ C := le_max_left C₀ (max 1 B)
    calc
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
          C₀ * Real.log t * (1 + M) := by simpa only [M] using hSource
      _ ≤ C * Real.log t * (1 + M) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀C hlogNonneg) hOneM
  · have htMem : t ∈ Set.Icc (10 : ℝ) K := by
      refine ⟨ht, ?_⟩
      dsimp only [K]
      exact le_max_of_le_right (le_of_not_ge hlarge)
    have htB : zetaMomentCriticalNorm t ^ (2 : ℕ) ≤ B :=
      hB ⟨t, htMem, rfl⟩
    have hBC : B ≤ C :=
      (le_max_right 1 B).trans (le_max_right C₀ (max 1 B))
    have hCnonneg : 0 ≤ C := hCpos.le
    calc
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤ B := htB
      _ ≤ C := hBC
      _ = C * 1 * 1 := by ring
      _ ≤ C * Real.log t * (1 + M) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (by linarith) hCnonneg)
          (by linarith) (by norm_num) (mul_nonneg hCnonneg hlogNonneg)

end MathCollab.Density.Stronger.PointMean
