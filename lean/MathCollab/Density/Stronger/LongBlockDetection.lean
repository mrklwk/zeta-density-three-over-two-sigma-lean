module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.WeightedCriticalMean
public import MathCollab.Density.Stronger.SmallResidue

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem negligible_residue_le_detector_height :
    ∀ᶠ T : ℝ in atTop, T^(-100 : ℝ) ≤ 1/(48*Real.log T) := by
  have ht := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 100)).tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/48))] with T hT hh
  have hTp : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hp : 48*Real.log T ≤ T^(100 : ℝ) := by
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hTp 100)).mp hh
    linarith
  rw [Real.rpow_neg hTp.le, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

/-- A genuinely large smooth block forces a weighted critical-line mean,
with a positive constant chosen before T and every block parameter. -/
theorem smoothMollifierBlock_eventually_detects_mean {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (ρ : ℂ) (X N q : ℝ),
      3/4 ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| →
      0 ≤ X → X ≤ T → 1 ≤ N → N ≤ T^2 → 0 ≤ q →
      1/(24*Real.log T) ≤ ‖smoothMollifierBlock ψ ρ X N q‖ →
      1/(48*Real.log T) ≤ C*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im := by
  obtain ⟨C,hC,h⟩ := uniform_smoothMollifierBlock_mean_bound hψ ha hb hs A hA
  refine ⟨C+1,by linarith,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    smoothDetectorResidue_eventually_small hψ ha hb hs, negligible_residue_le_detector_height]
    with T hT hres hsmall
  intro ρ X N q hβ hβ' hγ hX hXT hN hNT hq hlarge
  have hNp : 0 < N := by linarith
  have hr := (hres ρ X N q hβ hβ'.le hγ hX hXT hN hNT hq).trans hsmall
  have hm := h ρ X N q hβ hβ' hX hNp hq
  have hj := weightedCriticalMean_nonneg A ρ.im
  have hh : C*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im ≤
      (C+1)*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im := by gcongr; linarith
  have he : 1/(24*Real.log T) = 2*(1/(48*Real.log T)) := by ring
  rw [he] at hlarge
  linarith

/-- Every original zero in the slab has a fixed-list smooth detecting block
which also forces the weighted mean. This is available before dividing the
list into short and long scales. -/
theorem smoothDetector_eventually_detects_mean {σ δ : ℝ}
    (hσ : 3/4 < σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      ∃ j ∈ smoothScaleIndices (detectorY σ T*(Real.log T)^2),
        detectorX δ T/2 < (2 : ℝ)^j ∧ 2 ≤ (2 : ℝ)^j ∧
        1/(24*Real.log T) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY σ T) j‖ ∧
        1/(48*Real.log T) ≤ C*Real.sqrt (detectorX δ T)*((2 : ℝ)^j)^(1/2-ρ.re)*
          weightedCriticalMean A ρ.im := by
  obtain ⟨C,hC,hm⟩ := smoothMollifierBlock_eventually_detects_mean smoothDyadicWeight_contDiff
    (by norm_num : (0:ℝ)<5/8) (by norm_num : (0:ℝ)<3/2) smoothDyadicWeight_tsupport A hA
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hm, log_sq_eventually_le_height,
    smoothDetector_eventually_large hσ hδ hδ'] with T hT hmean hlogSq hdetect
  intro ρ hβ hβ' hγ hγ' hzero
  obtain ⟨j,hj,hXj,hlarge⟩ := hdetect ρ hβ hβ' hγ hγ' hzero
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hjpos : 0 < j := by
    by_contra hn
    rw [smoothDetectorBlock_zero_of_nonpos _ _ _ (not_lt.mp hn),norm_zero] at hlarge
    have : 0 < 1/(24*Real.log T) := by positivity
    linarith
  have hN : 2 ≤ (2 : ℝ)^j := by
    have hh := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show (1:ℤ) ≤ j by omega)
    simpa using hh
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTp.le _
  have hXT : detectorX δ T ≤ T := by
    simpa only [detectorX,Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show δ ≤ 1 by linarith)
  have hYp : 0 < detectorY σ T := Real.rpow_pos_of_pos hTp _
  have hYT : detectorY σ T ≤ T := by
    simpa only [detectorY,Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (smoothingExponent_lt_one hσ).le
  have hNT : (2 : ℝ)^j ≤ T^2 := by
    apply (mem_smoothScaleIndices.mp hj).2.trans
    calc
      _ ≤ T*T := mul_le_mul hYT hlogSq (sq_nonneg _) hTp.le
      _ = _ := by ring
  refine ⟨j,hj,hXj,hN,hlarge,?_⟩
  apply hmean ρ (detectorX δ T) ((2 : ℝ)^j) ((2 : ℝ)^j/detectorY σ T)
    (hσ.le.trans hβ) hβ' hγ hX hXT (by linarith) hNT (by positivity)
  rw [← smoothDetectorBlock_eq_smoothMollifierBlock (detectorX δ T) hYp (by linarith) hN]
  exact hlarge

end MathCollab.Density.Stronger
