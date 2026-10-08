module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.Parameters
public import MathCollab.Density.DetectorTruncation
public import MathCollab.Density.WeylInput

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The residue is uniformly negligible for all independent scales 0 ≤ X ≤ T
and 1 ≤ Y ≤ T. No moment estimate is used. -/
theorem norm_residue_le {ρ : ℂ} {X Y T : ℝ}
    (hT : 1 ≤ T) (hX : 0 ≤ X) (hXT : X ≤ T)
    (hY : 1 ≤ Y) (hYT : Y ≤ T)
    (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : T ≤ |ρ.im|) (hγ' : |ρ.im| ≤ 2*T) :
    ‖detectorResidue ρ X Y‖ ≤ 72*T^3*Real.exp (-T) := by
  have hTpos : 0 < T := by linarith
  have hsqrt : Real.sqrt X ≤ T := by
    apply (Real.sqrt_le_left hTpos.le).2
    nlinarith
  have hpower : Y^(1-ρ.re) ≤ T := by
    calc
      _ ≤ Y := by
        simpa using Real.rpow_le_rpow_of_exponent_le hY
          (show 1-ρ.re ≤ 1 by linarith)
      _ ≤ T := hYT
  have he : Real.exp (-|ρ.im|) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith)
  have hb := norm_detectorResidue_le hX (by linarith : 0 < Y) hβ hβ' (hT.trans hγ)
  calc
    _ ≤ 24*Real.sqrt X*Y^(1-ρ.re)*(1+|ρ.im|)*Real.exp (-|ρ.im|) := hb
    _ ≤ 24*T*T*(3*T)*Real.exp (-T) := by
      gcongr
      linarith
    _ = _ := by ring

/-- The actual contour detector is uniformly small for the stronger curve's
parameters. The Weyl input is proved and discharged; no moment is assumed. -/
theorem detector_eventually_small {σ δ ε : ℝ}
    (hσ : 3/4 < σ) (hδ : δ ≤ 1/8) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY σ T)‖ < ε := by
  obtain ⟨C, hC, hW⟩ := actual_zeta_weyl_input (by norm_num : (0 : ℝ) < 1/96)
  obtain ⟨A, hA, hbound⟩ := uniform_detector_integral_bound
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/96)).const_mul (A*C)
  simp only [mul_zero] at ht
  have hsmall : ∀ᶠ T : ℝ in atTop, A*C*T^(-1/48+1/96 : ℝ) < ε/2 := by
    have hexp : (-1/48+1/96 : ℝ) = -(1/96 : ℝ) := by norm_num
    rw [hexp]
    exact ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2))
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 72
  simp only [mul_zero] at hp
  have hpole : ∀ᶠ T : ℝ in atTop, 72*T^3*Real.exp (-T) < ε/2 := by
    simpa only [mul_zero, mul_assoc] using
      hp.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, hpole] with T hT hs hp
  intro ρ hβ hβ' hγ hγ' hzero
  have hTpos : 0 < T := by linarith
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTpos.le _
  have hXT : detectorX δ T ≤ T := by
    simpa [detectorX] using Real.rpow_le_rpow_of_exponent_le hT
      (show δ ≤ 1 by linarith)
  have hY : 1 ≤ detectorY σ T := Real.one_le_rpow hT (smoothingExponent_pos hσ).le
  have hYT : detectorY σ T ≤ T := by
    simpa [detectorY] using Real.rpow_le_rpow_of_exponent_le hT
      (smoothingExponent_lt_one hσ).le
  have hb : 3/4 ≤ ρ.re := hσ.le.trans hβ
  have hi := hbound (1/6+1/96) C T (detectorX δ T) (detectorY σ T) ρ
    (by norm_num) (by norm_num) hC.le hT hX (by linarith) hb hβ'.le hγ' hW
  have hscale := mul_le_mul_of_nonneg_left
    (detector_error_scale (η := 1/96) hσ hδ hT hβ) (show 0 ≤ A*C by positivity)
  have hint : ‖detectorIntegral ρ (detectorX δ T) (detectorY σ T)‖ < ε/2 :=
    (hi.trans (by simpa only [mul_assoc] using hscale)).trans_lt hs
  have hr := (norm_residue_le hT hX hXT hY hYT hb hβ'.le hγ hγ').trans_lt hp
  rw [smoothedDetector_contour_identity hY hb hβ' hzero]
  change ‖detectorResidue ρ (detectorX δ T) (detectorY σ T) +
    detectorIntegral ρ (detectorX δ T) (detectorY σ T)‖ < ε
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- The literal exponentially smoothed series after removal of its n=1 term.
Terms with 2 ≤ n ≤ X vanish by the proved Möbius identity. -/
def detectorTail (ρ : ℂ) (X Y : ℝ) : ℂ :=
  ∑' n : ℕ, detectorTerm ρ X Y (n+2)

theorem detectorTail_decomposition {ρ : ℂ} {X Y : ℝ}
    (hX : 1 ≤ X) (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    (Real.exp (-1/Y) : ℂ) + detectorTail ρ X Y = smoothedDetector ρ X (1/Y) := by
  have hs := summable_zeta_detector_series X hY hρ
  have he := hs.sum_add_tsum_nat_add 2
  have hz : detectorTerm ρ X Y 0 = 0 := by simp [detectorTerm, mollifierCoefficient]
  have ho : detectorTerm ρ X Y 1 = (Real.exp (-1/Y) : ℂ) := by
    simp [detectorTerm, mollifierCoefficient_one hX]
  have hfull : (∑' n : ℕ, detectorTerm ρ X Y n) = smoothedDetector ρ X (1/Y) := by
    apply tsum_congr
    intro n
    exact (smoothedDetector_term_eq ρ X Y n).symm
  change (∑ n ∈ Finset.range 2, detectorTerm ρ X Y n) + detectorTail ρ X Y =
    (∑' n : ℕ, detectorTerm ρ X Y n) at he
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hz, ho, hfull] using he

/-- Uniform detection of every actual zero in the slab, with the exact new
parameters and the same ordinate. This does not yet choose a smooth dyadic block. -/
theorem detectorTail_eventually_large {σ δ : ℝ}
    (hσ : 3/4 < σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      (1/2 : ℝ) ≤ ‖detectorTail ρ (detectorX δ T) (detectorY σ T)‖ := by
  have hy : ∀ᶠ T : ℝ in atTop, 4 ≤ detectorY σ T :=
    (tendsto_rpow_atTop (smoothingExponent_pos hσ)).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hy,
    detector_eventually_small hσ hδ' (by norm_num : (0 : ℝ) < 1/4)] with T hT hY hs
  intro ρ hβ hβ' hγ hγ' hzero
  have hX : 1 ≤ detectorX δ T := Real.one_le_rpow hT hδ
  have hd := detectorTail_decomposition hX (show 0 < detectorY σ T by linarith)
    (show 0 ≤ ρ.re by linarith)
  have he : (3/4 : ℝ) ≤ Real.exp (-1 / detectorY σ T) := by
    have hexp := Real.add_one_le_exp (-1 / detectorY σ T)
    have hinv : 1 / detectorY σ T ≤ (1/4 : ℝ) :=
      (div_le_iff₀ (by linarith : 0 < detectorY σ T)).2 (by linarith)
    rw [neg_div] at hexp ⊢
    linarith
  have hn : ‖(Real.exp (-1 / detectorY σ T) : ℂ)‖ ≤
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY σ T)‖ +
        ‖detectorTail ρ (detectorX δ T) (detectorY σ T)‖ := by
    have hh : (Real.exp (-1 / detectorY σ T) : ℂ) =
        smoothedDetector ρ (detectorX δ T) (1 / detectorY σ T) -
          detectorTail ρ (detectorX δ T) (detectorY σ T) := by rw [← hd]; ring
    rw [hh]
    exact norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  have hm := hs ρ hβ hβ' hγ hγ' hzero
  linarith

end MathCollab.Density.Stronger
