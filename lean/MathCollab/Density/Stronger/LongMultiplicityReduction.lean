module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.ShortZeroCount
public import MathCollab.Density.Stronger.LongMeanCounting

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Complex Set Filter MeasureTheory
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MathCollab.Density.Stronger

/-- Actual slab zeros outside the already counted short family. -/
def smoothLongZeroFinset (η σ δ T : ℝ) : Finset ℂ :=
  zetaZeroFinset σ T (2*T) \ smoothShortZeroFinset η σ δ T

/-- The complementary part keeps the original analytic multiplicity. -/
def smoothLongZeroCount (η σ δ T : ℝ) : ℕ :=
  ∑ ρ ∈ smoothLongZeroFinset η σ δ T, zetaMultiplicity ρ

theorem smoothLongZeroFinset_subset (η σ δ T : ℝ) :
    smoothLongZeroFinset η σ δ T ⊆ zetaZeroFinset σ T (2*T) := Finset.sdiff_subset

/-- Exact partition of every actual slab zero and all its analytic multiplicity. -/
theorem smooth_zeroCount_partition (η σ δ T : ℝ) :
    zetaSlabCount σ T (2*T) = smoothShortZeroCount η σ δ T + smoothLongZeroCount η σ δ T := by
  unfold zetaSlabCount smoothShortZeroCount smoothLongZeroCount smoothLongZeroFinset
  have hs := Finset.sum_sdiff (smoothShortZeroFinset_subset η σ δ T)
    (f := zetaMultiplicity)
  omega

/-- One critical-mean constant precedes the height and every complementary zero. -/
theorem smoothLongZeroFinset_eventually_detects_mean {σ δ η : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ smoothLongZeroFinset η σ δ T,
      (detectorY σ T)^((σ-1/2)/2) ≤
        48*C*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean 128 ρ.im := by
  obtain ⟨C, hC, hcover⟩ := smooth_long_mean_or_short_powered_cover hσ hσ' hδ hδ' hη 128 (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ), hcover] with T hT hc
  intro ρ hρ
  obtain ⟨hzmem, hnot⟩ := Finset.mem_sdiff.mp hρ
  obtain ⟨hz, hβ, hγ, hγ'⟩ := mem_zetaZeroFinset.mp hzmem
  have habs : |ρ.im| = ρ.im := abs_of_nonneg (hT.trans hγ)
  rcases hc ρ hβ hz.2.2 (by rwa [habs]) (by rwa [habs]) hz.1 with hmean | hshort
  · exact hmean
  · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hzmem, hshort⟩))

/-- Unconditional restoration of the complementary analytic-multiplicity count
from separated long detectors. The right side is the literal physical twelfth
moment, not a supplied moment bound. -/
theorem smoothLongZeroCount_physical_moment_reduction {σ δ η : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothLongZeroCount η σ δ T : ℝ)*(detectorY σ T)^(6*σ-3) ≤
        C*(detectorX δ T)^6*(Real.log T)^13*
          ((∫ t in Set.Icc 0 (3*T), zetaMomentCriticalNorm t^12)+T^(-113 : ℝ)) := by
  classical
  obtain ⟨Cm, hCm, hmean⟩ := smoothLongZeroFinset_eventually_detects_mean hσ hσ' hδ hδ' hη
  obtain ⟨Cb, hCb, hlocal⟩ := zeta_local_multiplicity_bound
  let A : ℝ := Real.pi^11*separationMass
  let B : ℝ := 2*(12 : ℝ)^12*Real.pi^12
  have hA : 0 ≤ A := mul_nonneg (by positivity) separationMass_nonneg
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ := 4*Cb*(48*Cm)^12*(A+B+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hmean] with T hT hm
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog2 : 0 ≤ Real.log (2*T) := Real.log_nonneg (by linarith)
  have hlogs : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    linarith
  have hbin (k : ℤ) : (∑ ρ ∈ (smoothLongZeroFinset η σ δ T).filter (fun ρ => ordinateBin ρ = k),
      (zetaMultiplicity ρ : ℝ)) ≤ Cb*Real.log (2*T) := by
    have hs : (smoothLongZeroFinset η σ δ T).filter (fun ρ => ordinateBin ρ = k) ⊆
        (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k) := by
      intro ρ hρ
      exact Finset.mem_filter.mpr
        ⟨smoothLongZeroFinset_subset η σ δ T (Finset.mem_filter.mp hρ).1, (Finset.mem_filter.mp hρ).2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
      (hlocal σ T hσ.le hT k)
  obtain ⟨R, hR, hcard, hsep, hcount⟩ := weighted_separated_extraction
    (smoothLongZeroFinset η σ δ T) (fun ρ => (zetaMultiplicity ρ : ℝ)) (by positivity : 0 ≤ Cb*Real.log (2*T)) hbin
  let U := R.image Complex.im
  have hUslab : ∀ u ∈ U, u ∈ Set.Icc T (2*T) := by
    intro u hu
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hu
    have hz := mem_zetaZeroFinset.mp (smoothLongZeroFinset_subset η σ δ T (hR hρ))
    exact ⟨hz.2.2.1, hz.2.2.2⟩
  have hUmean : ∀ u ∈ U, (detectorY σ T)^((σ-1/2)/2) ≤
      48*Cm*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean 128 u := by
    intro u hu
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hu
    exact hm ρ (hR hρ)
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTpos.le _
  have hY : 0 < detectorY σ T := Real.rpow_pos_of_pos hTpos _
  have hphysical := long_mean_count_le_physical_moment hT1 hX hY hsep hUslab hUmean
  let I : ℝ := ∫ t in Set.Icc 0 (3*T), zetaMomentCriticalNorm t^12
  have hI : 0 ≤ I := integral_nonneg (fun t => by positivity)
  have htail : 0 ≤ T^(-113 : ℝ) := Real.rpow_nonneg hTpos.le _
  have hmoment : A*I+B*T^(-113 : ℝ) ≤ (A+B+1)*(I+T^(-113 : ℝ)) := by
    nlinarith [mul_nonneg hA htail, mul_nonneg hB hI]
  have hcount' : (smoothLongZeroCount η σ δ T : ℝ) ≤ 2*(Cb*Real.log (2*T))*(U.card : ℝ) := by
    rw [← hcard] at hcount
    simpa only [smoothLongZeroCount, Nat.cast_sum] using hcount
  have hscale : 0 ≤ (detectorY σ T)^(6*σ-3) := Real.rpow_nonneg hY.le _
  have hh := mul_le_mul_of_nonneg_right hcount' hscale
  have hphysical' := mul_le_mul_of_nonneg_left hphysical
    (show 0 ≤ 2*(Cb*Real.log (2*T)) by positivity)
  have hpoly : 0 ≤ (48*Cm)^12*(detectorX δ T)^6*(Real.log T)^12 := by positivity
  have hbracket : 0 ≤ A*I+B*T^(-113 : ℝ) :=
    add_nonneg (mul_nonneg hA hI) (mul_nonneg hB htail)
  have hlogmul := mul_le_mul_of_nonneg_right hlogs
    (show 0 ≤ 2*Cb*((48*Cm)^12*(detectorX δ T)^6*(Real.log T)^12)*(A*I+B*T^(-113 : ℝ)) from
      mul_nonneg (mul_nonneg (by positivity) hpoly) hbracket)
  calc
    _ ≤ (2*(Cb*Real.log (2*T))*(U.card : ℝ))*(detectorY σ T)^(6*σ-3) := hh
    _ = (2*(Cb*Real.log (2*T)))*((U.card : ℝ)*(detectorY σ T)^(6*σ-3)) := by ring
    _ ≤ (2*(Cb*Real.log (2*T)))*
        ((48*Cm)^12*(detectorX δ T)^6*(Real.log T)^12*(A*I+B*T^(-113 : ℝ))) := hphysical'
    _ ≤ (4*Cb*(48*Cm)^12)*(detectorX δ T)^6*(Real.log T)^13*(A*I+B*T^(-113 : ℝ)) := by
      nlinarith only [hlogmul]
    _ ≤ (4*Cb*(48*Cm)^12)*(detectorX δ T)^6*(Real.log T)^13*
        ((A+B+1)*(I+T^(-113 : ℝ))) := mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by dsimp [C, I]; ring

end MathCollab.Density.Stronger
