module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.UniformMellin
public import MathCollab.Density.DetectorMellin

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open scoped BigOperators ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem LSeries_term_mul_scaled_cpow (f : ℕ → ℂ) (ρ s : ℂ)
    {N : ℝ} (hN : 0 < N) (n : ℕ) :
    LSeries.term f ρ n * (((n : ℝ)/N : ℝ) : ℂ)^(-s) =
      (N : ℂ)^s * LSeries.term f (ρ+s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [GammaMellin.cpow_neg_div_eq_reverse_cpow hnPos hN, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hN.le hnPos.le,
    LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    Complex.cpow_add _ _ hnC]
  simp only [Complex.ofReal_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem norm_LSeries_term_vertical (f : ℕ → ℂ) (ρ : ℂ) (σ u : ℝ) (n : ℕ) :
    ‖LSeries.term f (ρ+((σ : ℂ)+u*I)) n‖ =
      ‖LSeries.term f (ρ+(σ : ℂ)) n‖ := by
  simp [LSeries.norm_term_eq]

theorem continuous_LSeries_term_vertical (f : ℕ → ℂ) (ρ : ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun u : ℝ => LSeries.term f (ρ+((σ : ℂ)+u*I)) n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [LSeries.term_of_ne_zero hn]
  exact continuous_const.div ((by fun_prop : Continuous
    (fun u : ℝ => ρ+((σ : ℂ)+u*I))).const_cpow (Or.inl hnC))
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))

theorem integrable_scaled_mellin_line {ψ : ℝ → ℝ} {a b N : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (hN : 0 < N) (σ q : ℝ) :
    Integrable (fun u : ℝ => (N : ℂ)^((σ : ℂ)+u*I) *
      mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I)) := by
  have hm := dampedCutoff_integrable_mellin_line hψ ha hb hs σ q
  have hpow : Continuous (fun u : ℝ => (N : ℂ)^((σ : ℂ)+u*I)) :=
    (by fun_prop : Continuous (fun u : ℝ => (σ : ℂ)+u*I)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
  refine (hm.norm.const_mul (N^σ)).mono'
    (hpow.aestronglyMeasurable.mul hm.aestronglyMeasurable) ?_
  filter_upwards with u
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp

/-- Every summand on the full vertical line is integrable, and the sum of
its L¹ norms is finite whenever the shifted Dirichlet series converges. -/
theorem smoothMellin_absolute_exchange {ψ : ℝ → ℝ} {a b N : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (hN : 0 < N) (q σ : ℝ)
    (f : ℕ → ℂ) (ρ : ℂ) (hSum : LSeriesSummable f (ρ+(σ : ℂ))) :
    (∀ n : ℕ, Integrable (fun u : ℝ =>
      ((N : ℂ)^((σ : ℂ)+u*I) *
        mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I)) *
          LSeries.term f (ρ+((σ : ℂ)+u*I)) n)) ∧
    Summable (fun n : ℕ => ∫ u : ℝ,
      ‖((N : ℂ)^((σ : ℂ)+u*I) *
        mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I)) *
          LSeries.term f (ρ+((σ : ℂ)+u*I)) n‖) := by
  let H : ℝ → ℂ := fun u => (N : ℂ)^((σ : ℂ)+u*I) *
    mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I)
  have hH : Integrable H := integrable_scaled_mellin_line hψ ha hb hs hN σ q
  constructor
  · intro n
    refine (hH.norm.mul_const ‖LSeries.term f (ρ+(σ : ℂ)) n‖).mono'
      (hH.aestronglyMeasurable.mul
        (continuous_LSeries_term_vertical f ρ σ n).aestronglyMeasurable) ?_
    filter_upwards with u
    rw [norm_mul, norm_LSeries_term_vertical]
  · have hNorm := summable_norm_iff.mpr hSum
    convert hNorm.mul_left (∫ u : ℝ, ‖H u‖) using 1
    funext n
    simp_rw [norm_mul, norm_LSeries_term_vertical, integral_mul_const]
    simp only [H, norm_mul]

/-- The complete Dirichlet-series contour is a Bochner integrable function. -/
theorem integrable_smoothLSeries_contour {ψ : ℝ → ℝ} {a b N : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (hN : 0 < N) (q σ : ℝ)
    (f : ℕ → ℂ) (ρ : ℂ) (hSum : LSeriesSummable f (ρ+(σ : ℂ))) :
    Integrable (fun u : ℝ => (N : ℂ)^((σ : ℂ)+u*I) *
      mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I) *
        LSeries f (ρ+((σ : ℂ)+u*I))) := by
  obtain ⟨hInt,hAbs⟩ := smoothMellin_absolute_exchange hψ ha hb hs hN q σ f ρ hSum
  convert integrable_tsum_of_summable_integral_norm hInt hAbs using 1
  funext u
  simp only [tsum_mul_left, LSeries]

/-- Exact smooth cutoff identity on any line where the shifted Dirichlet
series converges absolutely. The series–integral exchange is proved above. -/
theorem smoothLSeries_eq_mellinContour {ψ : ℝ → ℝ} {a b N : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (hN : 0 < N) (q σ : ℝ)
    (f : ℕ → ℂ) (ρ : ℂ) (hSum : LSeriesSummable f (ρ+(σ : ℂ))) :
    (∑' n : ℕ, LSeries.term f ρ n * (dampedCutoff ψ q ((n : ℝ)/N) : ℂ)) =
      ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        (N : ℂ)^((σ : ℂ)+u*I) *
          mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I) *
            LSeries f (ρ+((σ : ℂ)+u*I)) := by
  let H : ℝ → ℂ := fun u => (N : ℂ)^((σ : ℂ)+u*I) *
    mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I)
  let F : ℕ → ℝ → ℂ := fun n u => H u * LSeries.term f (ρ+((σ : ℂ)+u*I)) n
  let C : ℂ := ((1/(2*Real.pi) : ℝ) : ℂ)
  obtain ⟨hInt,hAbs⟩ := smoothMellin_absolute_exchange hψ ha hb hs hN q σ f ρ hSum
  have hTerm (n : ℕ) :
      LSeries.term f ρ n * (dampedCutoff ψ q ((n : ℝ)/N) : ℂ) =
        C * ∫ u : ℝ, F n u := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [dampedCutoff_mellin_inversion hψ ha hb hs σ q (div_pos hnPos hN)]
    calc
      _ = C * ∫ u : ℝ, LSeries.term f ρ n *
          ((((n : ℝ)/N : ℝ) : ℂ)^(-((σ : ℂ)+u*I)) *
            mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+u*I)) := by
        rw [integral_const_mul]
        dsimp [C]
        ring
      _ = C * ∫ u : ℝ, F n u := by
        congr 1
        apply integral_congr_ae
        filter_upwards with u
        rw [← mul_assoc, LSeries_term_mul_scaled_cpow f ρ _ hN]
        dsimp [F,H]
        ring
  calc
    _ = ∑' n : ℕ, C * ∫ u : ℝ, F n u := tsum_congr hTerm
    _ = C * ∫ u : ℝ, ∑' n : ℕ, F n u := by
      rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hInt hAbs]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      simp only [F, tsum_mul_left, H, LSeries]

/-- Literal smooth mollifier block; damping q remains independent of N. -/
def smoothMollifierBlock (ψ : ℝ → ℝ) (ρ : ℂ) (X N q : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (mollifierDirichletCoeff X) ρ n *
    (dampedCutoff ψ q ((n : ℝ)/N) : ℂ)

/-- Full right-line representation by the actual zeta–Möbius product.
Neither a zero hypothesis nor a moment estimate is needed. -/
theorem smoothMollifierBlock_eq_rightContour {ψ : ℝ → ℝ} {a b N : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (hN : 0 < N) (q X : ℝ)
    {ρ : ℂ} (hρ : 3/4 ≤ ρ.re) :
    smoothMollifierBlock ψ ρ X N q =
      ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        (N : ℂ)^(((1/2 : ℝ) : ℂ)+u*I) *
          mellin (fun y => (dampedCutoff ψ q y : ℂ)) (((1/2 : ℝ) : ℂ)+u*I) *
            zetaMollifier X (ρ+(((1/2 : ℝ) : ℂ)+u*I)) *
              riemannZeta (ρ+(((1/2 : ℝ) : ℂ)+u*I)) := by
  rw [smoothMollifierBlock, smoothLSeries_eq_mellinContour hψ ha hb hs hN q (1/2)
    (mollifierDirichletCoeff X) ρ
    (mollifierDirichletCoeff_LSeriesSummable X (by simp; linarith))]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [← riemannZeta_mul_zetaMollifier_eq_LSeries X (by simp; linarith)]
  ring

/-- Absolute convergence of the literal right-line zeta–Möbius contour. -/
theorem integrable_smoothMollifierBlock_rightContour {ψ : ℝ → ℝ} {a b N : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (hN : 0 < N) (q X : ℝ)
    {ρ : ℂ} (hρ : 3/4 ≤ ρ.re) :
    Integrable (fun u : ℝ => (N : ℂ)^(((1/2 : ℝ) : ℂ)+u*I) *
      mellin (fun y => (dampedCutoff ψ q y : ℂ)) (((1/2 : ℝ) : ℂ)+u*I) *
        zetaMollifier X (ρ+(((1/2 : ℝ) : ℂ)+u*I)) *
          riemannZeta (ρ+(((1/2 : ℝ) : ℂ)+u*I))) := by
  have h := integrable_smoothLSeries_contour hψ ha hb hs hN q (1/2)
    (mollifierDirichletCoeff X) ρ
    (mollifierDirichletCoeff_LSeriesSummable X (by simp; linarith))
  apply h.congr
  filter_upwards with u
  rw [← riemannZeta_mul_zetaMollifier_eq_LSeries X (by simp; linarith)]
  ring

end MathCollab.Density.Stronger
