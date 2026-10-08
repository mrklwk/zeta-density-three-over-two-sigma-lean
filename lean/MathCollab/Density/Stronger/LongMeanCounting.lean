module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.LongMeanScale
public import MathCollab.Density.Stronger.SeparatedCriticalSampling
public import MathCollab.Density.Stronger.LongBlockDetection
public import MathCollab.Density.Stronger.ShortPoweredFamily

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Filter MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The long-scale lower bound gives this finite counting inequality before
any moment estimate is used. -/
theorem long_mean_twelfth_count {A : ℕ} {U : Finset ℝ} {C X Y T σ : ℝ}
    (hX : 0 ≤ X) (hY : 0 < Y)
    (hmean : ∀ u ∈ U, Y^((σ-1/2)/2) ≤
      48*C*Real.sqrt X*Real.log T*weightedCriticalMean A u) :
    (U.card : ℝ)*Y^(6*σ-3) ≤
      (48*C)^12*X^6*(Real.log T)^12 * ∑ u ∈ U, (weightedCriticalMean A u)^12 := by
  have hscale : (Y^((σ-1/2)/2))^12 = Y^(6*σ-3) := by
    rw [← Real.rpow_mul_natCast hY.le]
    congr 1
    norm_num
    ring
  have hsqrt : (Real.sqrt X)^12 = X^6 := by
    calc
      _ = ((Real.sqrt X)^2)^6 := by ring
      _ = _ := by rw [Real.sq_sqrt hX]
  have hh (u : ℝ) (hu : u ∈ U) :
      Y^(6*σ-3) ≤ (48*C)^12*X^6*(Real.log T)^12*(weightedCriticalMean A u)^12 := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hY.le ((σ-1/2)/2)) (hmean u hu) 12
    rw [hscale] at hp
    simpa only [mul_pow, hsqrt] using hp
  have hh' := Finset.sum_le_sum hh
  simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] using hh'

/-- The actual-zero dichotomy with the long alternative expressed as a
critical-line mean. Both alternatives keep the original ordinate. -/
theorem smooth_long_mean_or_short_powered_cover {σ δ η : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η)
    (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      ((detectorY σ T)^((σ-1/2)/2) ≤
        48*C*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean A ρ.im) ∨
      (∃ q ∈ smoothPoweredIndices σ δ T,
        (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (smoothPoweredFamilyScale q)
            (smoothPoweredFamilyCoefficient η σ δ T q) ρ.im‖) := by
  obtain ⟨C,hC,hm⟩ := smoothMollifierBlock_eventually_detects_mean smoothDyadicWeight_contDiff
    (by norm_num : (0:ℝ)<5/8) (by norm_num : (0:ℝ)<3/2) smoothDyadicWeight_tsupport A hA
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hm, log_sq_eventually_le_height,
    smooth_long_or_short_powered_cover hσ hσ' hδ hδ' hη] with T hT hmean hlogSq hcover
  intro ρ hβ hβ' hγ hγ' hzero
  rcases hcover ρ hβ hβ' hγ hγ' hzero with ⟨j,hj,hlong,hlarge⟩ | hshort
  · apply Or.inl
    have hTp : 0 < T := by linarith
    have hT1 : 1 ≤ T := by linarith
    have hlog : 0 < Real.log T := Real.log_pos (by linarith)
    have hjpos : 0 < j := smoothDetectorBlock_index_pos
      (show smoothDetectorBlock ρ (detectorX δ T) (detectorY σ T) j ≠ 0 by
        intro hz
        rw [hz,norm_zero] at hlarge
        have : 0 < 1/(24*Real.log T) := by positivity
        linarith)
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
    have hlong' : Real.sqrt (detectorY σ T) ≤ (2 : ℝ)^j := by
      have he : Real.sqrt (detectorY σ T) = T^(smoothingExponent σ/2) := by
        rw [Real.sqrt_eq_rpow,detectorY,← Real.rpow_mul hTp.le]
        congr 1
        ring
      rw [he]
      exact hlong.le
    apply weightedCriticalMean_long_scale (by linarith) (by linarith) hYp
      (by linarith : 1/2 ≤ σ) hβ hlong'
    apply hmean ρ (detectorX δ T) ((2 : ℝ)^j) ((2 : ℝ)^j/detectorY σ T)
      (hσ.le.trans hβ) hβ' hγ hX hXT (by linarith) hNT (by positivity)
    rw [← smoothDetectorBlock_eq_smoothMollifierBlock (detectorX δ T) hYp (by linarith) hN]
    exact hlarge
  · exact Or.inr hshort

/-- The unconditional long-count reduction ends at the literal physical
zeta moment. There is no premise asserting a bound on that moment. -/
theorem long_mean_count_le_physical_moment {U : Finset ℝ} {C X Y T σ : ℝ}
    (hT : 1 ≤ T) (hX : 0 ≤ X) (hY : 0 < Y)
    (hU : oneSeparated U) (hslab : ∀ u ∈ U, u ∈ Set.Icc T (2*T))
    (hmean : ∀ u ∈ U, Y^((σ-1/2)/2) ≤
      48*C*Real.sqrt X*Real.log T*weightedCriticalMean 128 u) :
    (U.card : ℝ)*Y^(6*σ-3) ≤ (48*C)^12*X^6*(Real.log T)^12 *
      (Real.pi^11 * separationMass * (∫ t in Set.Icc 0 (3*T), zetaMomentCriticalNorm t^12) +
        (2*(12:ℝ)^12*Real.pi^12)*T^(-113 : ℝ)) := by
  apply (long_mean_twelfth_count hX hY hmean).trans
  exact mul_le_mul_of_nonneg_left (separated_weightedCriticalMean_twelfth_le hT hU hslab)
    (by positivity)

end MathCollab.Density.Stronger
