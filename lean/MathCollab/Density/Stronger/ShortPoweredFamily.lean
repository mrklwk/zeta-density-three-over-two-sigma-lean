module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.ShortPoweredHeight

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- This bound is fixed by sigma and delta, before T and any zero. -/
def smoothPowerBound (σ δ : ℝ) : ℕ := ⌈2*lowerExponent σ/δ⌉₊

def smoothPoweredFamilyScale (q : (ℤ × ℕ × ℕ) × ℕ × ℕ) : ℕ :=
  2^q.2.2*(smoothHalfScale q.1.1 q.1.2.1)^q.2.1

/-- The complete finite powered family, restricted by scale conditions that
are independent of the zero. The original smooth scale remains in q.1.1. -/
def smoothPoweredIndices (σ δ T : ℝ) : Finset ((ℤ × ℕ × ℕ) × ℕ × ℕ) :=
  ((smoothTaylorIndices σ T).product
    ((Finset.Icc 1 (smoothPowerBound σ δ)).product (Finset.range (smoothPowerBound σ δ)))).filter
    (fun q => q.2.2 < q.2.1 ∧
      T^(lowerExponent σ) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent σ))

def smoothPoweredFamilyCoefficient (η σ δ T : ℝ) (q : (ℤ × ℕ × ℕ) × ℕ × ℕ) (n : ℕ) : ℂ :=
  normalizedSmoothPoweredCoefficient η T (detectorX δ T) (detectorY σ T)
    q.1.1 q.1.2.1 q.1.2.2 q.2.1 n

theorem smoothPoweredFamilyScale_pos (q : (ℤ × ℕ × ℕ) × ℕ × ℕ) :
    0 < smoothPoweredFamilyScale q := by
  unfold smoothPoweredFamilyScale
  exact mul_pos (by positivity) (pow_pos (smoothHalfScale_pos _ _) _)

theorem mem_smoothPoweredIndices {σ δ T : ℝ} {q : (ℤ × ℕ × ℕ) × ℕ × ℕ} :
    q ∈ smoothPoweredIndices σ δ T ↔
      q.1 ∈ smoothTaylorIndices σ T ∧
      1 ≤ q.2.1 ∧ q.2.1 ≤ smoothPowerBound σ δ ∧ q.2.2 < q.2.1 ∧
      T^(lowerExponent σ) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent σ) := by
  constructor
  · intro hq
    obtain ⟨hbase, hlt, hlo, hhi⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp, hkl⟩ := Finset.mem_product.mp hbase
    obtain ⟨hk, hl⟩ := Finset.mem_product.mp hkl
    have hk' := Finset.mem_Icc.mp hk
    exact ⟨hp, hk'.1, hk'.2, hlt, hlo, hhi⟩
  · rintro ⟨hp, hk0, hkK, hl, hlo, hhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hp, Finset.mem_product.mpr ?_⟩, hl, hlo, hhi⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hk0, hkK⟩, Finset.mem_range.mpr (lt_of_lt_of_le hl hkK)⟩

theorem smoothTaylorIndices_card_eventually {σ : ℝ} (hσ : 3/4 < σ) :
    ∀ᶠ T : ℝ in atTop, ((smoothTaylorIndices σ T).card : ℝ) ≤ 144*(Real.log T)^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    log_sq_eventually_le_height] with T hT hlog hsq
  have hYlo : 1 ≤ detectorY σ T := Real.one_le_rpow hT (smoothingExponent_pos hσ).le
  have hYhi : detectorY σ T ≤ T := by
    simpa only [detectorY, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (smoothingExponent_lt_one hσ).le
  have hR : 1 ≤ detectorY σ T*(Real.log T)^2 := by nlinarith
  have hRhi : detectorY σ T*(Real.log T)^2 ≤ T^2 := by nlinarith
  exact smoothTaylorIndices_card_le_log (smoothScaleIndices_card_le_log hT hlog hR hRhi) hlog

/-- At most a fixed multiple of log(T)^2 members, before zeros are selected. -/
theorem smoothPoweredIndices_card_eventually {σ : ℝ} (hσ : 3/4 < σ) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ((smoothPoweredIndices σ δ T).card : ℝ) ≤
        144*(smoothPowerBound σ δ : ℝ)^2*(Real.log T)^2 := by
  filter_upwards [smoothTaylorIndices_card_eventually hσ] with T hcard
  have hh := Finset.card_le_card (Finset.filter_subset
    (fun q : (ℤ × ℕ × ℕ) × ℕ × ℕ => q.2.2 < q.2.1 ∧
      T^(lowerExponent σ) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent σ))
    ((smoothTaylorIndices σ T).product
      ((Finset.Icc 1 (smoothPowerBound σ δ)).product (Finset.range (smoothPowerBound σ δ)))))
  have hc : ((smoothPoweredIndices σ δ T).card : ℝ) ≤
      ((smoothTaylorIndices σ T).card : ℝ)*(smoothPowerBound σ δ : ℝ)^2 := by
    exact_mod_cast (by simpa [smoothPoweredIndices, Nat.card_Icc, pow_two] using hh)
  calc
    _ ≤ ((smoothTaylorIndices σ T).card : ℝ)*(smoothPowerBound σ δ : ℝ)^2 := hc
    _ ≤ (144*(Real.log T)^2)*(smoothPowerBound σ δ : ℝ)^2 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- Every member of the fixed family has the required powered scales and
globally bounded normalized coefficients. Threshold precedes every index. -/
theorem smoothPoweredFamily_admissible {σ η : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ q ∈ smoothPoweredIndices σ δ T,
      T^(lowerExponent σ) ≤ (smoothPoweredFamilyScale q : ℝ) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ (2 : ℝ)^(smoothPowerBound σ δ)*T^(smoothingExponent σ) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ T ∧
      ∀ n : ℕ, ‖smoothPoweredFamilyCoefficient η σ δ T q n‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    fixed_scale_factor_eventually_below_height (C := (2 : ℝ)^(smoothPowerBound σ δ)) (smoothingExponent_lt_one hσ),
    normalizedSmoothPoweredCoefficient_eventually hη (smoothPowerBound σ δ)] with T hT hupper hnorm
  intro q hq
  obtain ⟨_, _, hkK, hl, hlo, hhi⟩ := mem_smoothPoweredIndices.mp hq
  have hs := bounded_power_piece_scales (Nat.cast_nonneg (smoothHalfScale q.1.1 q.1.2.1)) hkK hl hlo hhi
  have he : (smoothPoweredFamilyScale q : ℝ) =
      (2 : ℝ)^q.2.2*(smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 := by
    simp [smoothPoweredFamilyScale]
  refine ⟨by rw [he]; exact hs.1, by rw [he]; exact hs.2, ?_, ?_⟩
  · rw [he]
    exact hs.2.trans hupper
  · have hsupp := bounded_power_support_scale
      (Nat.cast_nonneg (smoothHalfScale q.1.1 q.1.2.1)) hkK hhi
    have hTpos : 0 < T := by linarith
    have hY : 0 < detectorY σ T := Real.rpow_pos_of_pos hTpos _
    exact hnorm (detectorX δ T) (detectorY σ T) q.1.1 q.1.2.1 q.1.2.2 q.2.1 hY hkK
      (hsupp.trans (hupper.trans (by nlinarith)))

/-- Complete actual-zero dichotomy: a long smooth detector, or a member of
the finite normalized powered short family at the original ordinate. -/
theorem smooth_long_or_short_powered_cover {σ δ η : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      (∃ j ∈ smoothScaleIndices (detectorY σ T*(Real.log T)^2),
        T^(smoothingExponent σ/2) < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY σ T) j‖) ∨
      (∃ q ∈ smoothPoweredIndices σ δ T,
        (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (smoothPoweredFamilyScale q) (smoothPoweredFamilyCoefficient η σ δ T q) ρ.im‖) := by
  have ha : 0 < lowerExponent σ := by unfold lowerExponent; positivity
  filter_upwards [smooth_long_or_short_Taylor_cover hσ hδ.le hδ',
    short_scale_bounded_power ha hδ,
    exists_normalizedSmoothPowered_height hη (smoothPowerBound σ δ)] with T hcover hpower hheight
  intro ρ hβ hβ' hγ hγ' hzero
  rcases hcover ρ hβ hβ' hγ hγ' hzero with hlong | ⟨p, hp, hlo, hhi, hdet⟩
  · exact Or.inl hlong
  · have hc : smoothingExponent σ/2 = 3*lowerExponent σ/4 := by rw [smoothingExponent_eq]; ring
    obtain ⟨k, hk, hkK, hklo, hkhi⟩ := hpower (smoothHalfScale p.1 p.2.1)
      hlo (by rw [← hc]; exact hhi)
    have hkK' : k ≤ smoothPowerBound σ δ := hkK
    have hupper : (smoothHalfScale p.1 p.2.1 : ℝ)^k ≤ T^(smoothingExponent σ) := by
      simpa only [← smoothingExponent_eq] using hkhi
    obtain ⟨l, hl, hh⟩ := hheight σ (detectorX δ T) (detectorY σ T) ρ.im
      p.1 p.2.1 p.2.2 k hσ'.le (by omega) hkK' hdet
    refine Or.inr ⟨(p,k,l), ?_, hh⟩
    exact mem_smoothPoweredIndices.mpr ⟨hp, hk, hkK', Finset.mem_range.mp hl, hklo, hupper⟩

end MathCollab.Density.Stronger
