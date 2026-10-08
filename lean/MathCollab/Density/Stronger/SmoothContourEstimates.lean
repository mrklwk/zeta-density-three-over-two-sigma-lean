module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothContour
public import MathCollab.Density.Stronger.UniformMellin
public import MathCollab.Density.DetectorEstimates

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open MathCollab.Density.ZetaGrowth MathCollab.Density.Contour
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Coarse actual-zeta growth on a vertical line with a fixed real gap from its pole. -/
theorem norm_riemannZeta_le_eight_mul_norm {s : ℂ}
    (hre : (1/4 : ℝ) ≤ s.re) (hgap : (1/4 : ℝ) ≤ |s.re-1|) :
    ‖riemannZeta s‖ ≤ 8*‖s‖ := by
  have hspos : 0 < s.re := by linarith
  have hs : s ≠ 1 := by intro h; norm_num [h] at hgap
  have hden : (1/4 : ℝ) ≤ ‖s-1‖ :=
    hgap.trans (by simpa using Complex.abs_re_le_norm (s-1))
  have hrem : ‖abelZetaRemainder s‖ ≤ 4 :=
    (norm_abelZetaRemainder_le hspos).trans ((div_le_iff₀ hspos).2 (by linarith))
  rw [riemannZeta_eq_abel hspos hs]
  calc
    _ ≤ ‖s/(s-1)‖ + ‖s*abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖/‖s-1‖ + ‖s‖*‖abelZetaRemainder s‖ := by rw [norm_div,norm_mul]
    _ ≤ ‖s‖/(1/4)+‖s‖*4 := add_le_add
      (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden)
      (mul_le_mul_of_nonneg_left hrem (norm_nonneg _))
    _ = 8*‖s‖ := by ring

theorem continuous_smoothDetectorKernel_line {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hs : tsupport ψ ⊆ Icc a b)
    (ρ : ℂ) (X q u : ℝ) {N : ℝ} (hN : 0 < N) (hp : ρ.re+u ≠ 1) :
    Continuous (fun t : ℝ => smoothDetectorKernel ψ ρ X N q ((u : ℂ)+(t : ℂ)*I)) := by
  let line := fun t : ℝ => (u : ℂ)+(t : ℂ)*I
  have hl : Continuous line := by dsimp [line]; fun_prop
  have hm : Continuous (mellin (fun y => (dampedCutoff ψ q y : ℂ))) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mp
      (dampedCutoff_mellin_entire hψ ha hs q)).continuous
  unfold smoothDetectorKernel
  apply Continuous.mul
  · apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.cpow continuous_const hl
        intro t
        left
        simpa using hN
      · exact hm.comp hl
    · apply continuous_iff_continuousAt.mpr
      intro t
      exact ContinuousAt.comp' (differentiableAt_zetaMollifier X (ρ+line t)).continuousAt
        (by fun_prop)
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt
      (by fun_prop)
    intro he
    apply hp
    have hh := congrArg Complex.re he
    simpa [line] using hh

/-- Absolute convergence on a fixed vertical line away from the zeta pole.
No moment or pointwise subconvexity hypothesis is used. -/
theorem integrable_smoothDetectorKernel_line {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (ρ : ℂ) (X u : ℝ) {N q : ℝ} (hN : 0 < N) (hq : 0 ≤ q)
    (hre : 1/4 ≤ ρ.re+u) (hgap : 1/4 ≤ |ρ.re+u-1|) :
    Integrable (fun t : ℝ => smoothDetectorKernel ψ ρ X N q ((u : ℂ)+(t : ℂ)*I)) := by
  let line := fun t : ℝ => (u : ℂ)+(t : ℂ)*I
  obtain ⟨_,_,h⟩ := dampedCutoff_uniform_mellin_weighted_L1 hψ ha hb hs u u 1
  have hmass := (h u ⟨le_rfl,le_rfl⟩ q hq).1
  simp only [pow_one] at hmass
  have hp : ρ.re+u ≠ 1 := by intro h; rw [h] at hgap; norm_num at hgap
  have hc := continuous_smoothDetectorKernel_line hψ ha hs ρ X q u hN hp
  let C : ℝ := N^u*(⌊X⌋₊ : ℝ)*8*(|ρ.re+u|+|ρ.im|+1)
  apply (hmass.const_mul C).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hre' : (ρ+line t).re = ρ.re+u := by simp [line]
  have him' : (ρ+line t).im = ρ.im+t := by simp [line]
  have hz := norm_riemannZeta_le_eight_mul_norm (s := ρ+line t)
    (by rw [hre']; exact hre) (by rw [hre']; exact hgap)
  have hn : ‖ρ+line t‖ ≤ (|ρ.re+u|+|ρ.im|+1)*(1+|t|) := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im (ρ+line t)
    rw [hre',him'] at hnorm
    have ht := abs_add_le ρ.im t
    nlinarith [mul_nonneg (abs_nonneg (ρ.re+u)) (abs_nonneg t),
      mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
  have hz' : ‖riemannZeta (ρ+line t)‖ ≤ 8*(|ρ.re+u|+|ρ.im|+1)*(1+|t|) := by
    nlinarith
  have hm := norm_zetaMollifier_le_cutoff X (s := ρ+line t) (by rw [hre']; linarith)
  change ‖(N : ℂ)^(line t) * mellin (fun y => (dampedCutoff ψ q y : ℂ)) (line t) *
    zetaMollifier X (ρ+line t) * riemannZeta (ρ+line t)‖ ≤ _
  rw [norm_mul,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  have hlr : (line t).re = u := by simp [line]
  rw [hlr]
  calc
    _ ≤ N^u*‖mellin (fun y => (dampedCutoff ψ q y : ℂ)) (line t)‖*(⌊X⌋₊ : ℝ)*
        (8*(|ρ.re+u|+|ρ.im|+1)*(1+|t|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hz'
        (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [C,line]; ring

theorem integrable_smoothDetectorKernel_left {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (ρ : ℂ) (X : ℝ) {N q : ℝ} (hN : 0 < N) (hq : 0 ≤ q) :
    Integrable (fun t : ℝ => smoothDetectorKernel ψ ρ X N q
      (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  apply integrable_smoothDetectorKernel_line hψ ha hb hs ρ X (1/2-ρ.re) hN hq
  · linarith
  · rw [show ρ.re+(1/2-ρ.re)-1 = -(1/2 : ℝ) by ring]
    norm_num

theorem integrable_smoothDetectorKernel_right {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    {ρ : ℂ} (X : ℝ) {N q : ℝ} (hN : 0 < N) (hq : 0 ≤ q) (hβ : 3/4 ≤ ρ.re) :
    Integrable (fun t : ℝ => smoothDetectorKernel ψ ρ X N q
      (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)) := by
  apply integrable_smoothDetectorKernel_line hψ ha hb hs ρ X (1/2) hN hq
  · linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ ρ.re+1/2-1)]
    linarith

/-- A stripwise horizontal majorant uniform in q≥0. -/
theorem smoothDetectorKernel_horizontal_bound {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    {ρ : ℂ} (X : ℝ) {N : ℝ} (hN : 0 < N) (hβ : ρ.re ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 0 ≤ q → ∀ u ∈ Icc (1/2-ρ.re) (1/2 : ℝ),
      ∀ t : ℝ, |ρ.im|+1 ≤ |t| →
        ‖smoothDetectorKernel ψ ρ X N q ((u : ℂ)+(t : ℂ)*I)‖ ≤ C/(1+|t|)^2 := by
  obtain ⟨B,hB,hdecay⟩ := dampedCutoff_uniform_mellin_decay hψ ha hb hs
    (1/2-ρ.re) (1/2) 3
  obtain ⟨P,hP⟩ := (isCompact_Icc : IsCompact (Icc (1/2-ρ.re) (1/2 : ℝ))).bddAbove_image
    (Real.continuous_const_rpow hN.ne').continuousOn
  let D := max P 0
  have hD : 0 ≤ D := le_max_right _ _
  let C : ℝ := D*B*(⌊X⌋₊ : ℝ)*5*(2+|ρ.im|)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q hq u hu t ht
  let s : ℂ := (u : ℂ)+(t : ℂ)*I
  have hre : (ρ+s).re = ρ.re+u := by simp [s]
  have him : (ρ+s).im = ρ.im+t := by simp [s]
  have him' : 1 ≤ |(ρ+s).im| := by
    rw [him]
    have h := abs_add_le (ρ.im+t) (-ρ.im)
    rw [show ρ.im+t+-ρ.im=t by ring, abs_neg] at h
    linarith
  have hz := norm_riemannZeta_le_five_mul_norm (s := ρ+s) (by rw [hre]; linarith [hu.1]) him'
  have hn : ‖ρ+s‖ ≤ 2+|ρ.im|+|t| := by
    have h := Complex.norm_le_abs_re_add_abs_im (ρ+s)
    rw [hre,him,abs_of_nonneg (show 0 ≤ ρ.re+u by linarith [hu.1])] at h
    have ht' := abs_add_le ρ.im t
    linarith [hu.2]
  have hz' : ‖riemannZeta (ρ+s)‖ ≤ 5*(2+|ρ.im|)*(1+|t|) := by
    nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t),abs_nonneg t]
  have hm := norm_zetaMollifier_le_cutoff X (s := ρ+s) (by rw [hre]; linarith [hu.1])
  have hp : ‖(N : ℂ)^s‖ ≤ D := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
    simpa [s,D] using (hP ⟨u,hu,rfl⟩).trans (le_max_left P (0:ℝ))
  have hd := hdecay u hu q hq t
  change ‖(N : ℂ)^s * mellin (fun y => (dampedCutoff ψ q y : ℂ)) s *
    zetaMollifier X (ρ+s) * riemannZeta (ρ+s)‖ ≤ _
  rw [norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (D*(B/(1+|t|)^3))*(⌊X⌋₊ : ℝ)*(5*(2+|ρ.im|)*(1+|t|)) :=
      mul_le_mul (mul_le_mul (mul_le_mul hp hd (norm_nonneg _) hD) hm
        (norm_nonneg _) (by positivity)) hz' (norm_nonneg _) (by positivity)
    _ = C/(1+|t|)^2 := by
      dsimp [C]
      have ht0 : 1+|t| ≠ 0 := ne_of_gt (by positivity : (0:ℝ) < 1+|t|)
      field_simp [ht0]

/-- Both horizontal edges tend to zero at infinite rectangle height. -/
theorem tendsto_smoothDetector_horizontal_integral {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    {ρ : ℂ} (X : ℝ) {N q ε : ℝ} (hN : 0 < N) (hq : 0 ≤ q)
    (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun R : ℝ => ∫ u in (1/2-ρ.re)..(1/2 : ℝ),
      smoothDetectorKernel ψ ρ X N q ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := smoothDetectorKernel_horizontal_bound hψ ha hb hs X hN hβ'
  have hlim : Tendsto (fun R : ℝ => C/(1+R)^2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_const_nhds.add_atTop tendsto_id)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (|ρ.im|+1)] with R hR
  have hRpos : 0 < R := by linarith [abs_nonneg ρ.im]
  have he : |ε*R| = R := by rw [abs_mul,hε,one_mul,abs_of_pos hRpos]
  have hlength : |(1/2 : ℝ)-(1/2-ρ.re)| ≤ 1 := by
    rw [show (1/2 : ℝ)-(1/2-ρ.re)=ρ.re by ring,
      abs_of_nonneg (show 0 ≤ ρ.re by linarith)]
    exact hβ'
  have hpoint : ∀ u ∈ Set.uIoc (1/2-ρ.re) (1/2 : ℝ),
      ‖smoothDetectorKernel ψ ρ X N q ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)‖ ≤ C/(1+R)^2 := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : 1/2-ρ.re ≤ (1/2 : ℝ))] at hu
    have h := hbound q hq u ⟨hu.1.le,hu.2⟩ (ε*R) (by rw [he]; exact hR)
    simpa only [he] using h
  have hmul := mul_le_mul_of_nonneg_left hlength (by positivity : 0 ≤ C/(1+R)^2)
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans (by simpa using hmul)

end MathCollab.Density.Stronger
