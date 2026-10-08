module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSignedPhaseSeries
public import MathCollab.Density.Stronger.Atkinson.AtkinsonDampedDyadic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonStationaryBlock (T G L : ℝ) (m N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, atkinsonStationaryLeadingTerm T G L (m+i)

theorem norm_atkinsonNegativePhaseBlockSum (T : ℝ) (m N : ℕ) :
    ‖∑ i ∈ Finset.range N, atkinsonNegativePhaseTerm T (m+i)‖ =
      ‖atkinsonPhaseBlockSum T m N‖ := by
  simp only [atkinsonNegativePhaseTerm_eq_conj,← map_sum,Complex.norm_conj]
  rfl

theorem atkinsonStationaryBlock_eq_signed {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (m N : ℕ) :
    atkinsonStationaryBlock T G L m N = atkinsonCommonMainPhase T *
      ((∑ i ∈ Finset.range N, atkinsonPositiveMainWeight T G L (m+i)*atkinsonPositivePhaseTerm T (m+i))-
        ∑ i ∈ Finset.range N, atkinsonNegativeMainWeight T G L (m+i)*atkinsonNegativePhaseTerm T (m+i)) := by
  unfold atkinsonStationaryBlock
  simp_rw [atkinsonStationaryLeadingTerm_eq_signed hT hG L]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]

theorem exists_norm_atkinsonStationaryBlock_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T → 0 < L →
      ∀ m N : ℕ, 0 < m → 10000*((m+N:ℕ):ℝ) ≤ T →
      ‖atkinsonStationaryBlock T G L m N‖ ≤
        C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))*
          atkinsonPhaseBlockMax T m N := by
  obtain ⟨C,hC,hvar⟩ := exists_finiteVariationBound_atkinsonMainWeights
  refine ⟨8*C,by positivity,?_⟩
  intro T G L hT hG hGT hL m N hm hN
  obtain ⟨hp,hn⟩ := hvar T G L hT hG hGT hL m N hm hN
  have hmax := atkinsonPhaseBlockMax_nonneg T m N
  have hpb := hp.norm_sum_mul_le hmax (fun j hj => norm_atkinsonPhaseBlockSum_le_max T m N j hj)
  have hnb := hn.norm_sum_mul_le hmax (fun j hj => by
    rw [norm_atkinsonNegativePhaseBlockSum]
    exact norm_atkinsonPhaseBlockSum_le_max T m N j hj)
  rw [atkinsonStationaryBlock_eq_signed hT hG.ne',norm_mul]
  apply (mul_le_mul (norm_atkinsonCommonMainPhase_le T) (norm_sub_le _ _)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans
  nlinarith

theorem exists_atkinsonSourceCutoff_block_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ∀ m N : ℕ, 0 < m → m+N ≤ atkinsonSourceCutoff T G (Real.log T) →
      ‖atkinsonStationaryBlock T G (Real.log T) m N‖ ≤
        C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))*
          atkinsonPhaseBlockMax T m N := by
  obtain ⟨C,hC,hblock⟩ := exists_norm_atkinsonStationaryBlock_le
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp (eventually_atkinsonSourceCutoff_small hδ)
  refine ⟨C,hC,max 40000 B,le_max_left _ _,?_⟩
  intro T G hT hlower hupper m N hm hcut
  have hTlarge : 40000 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hGhi : G ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact hupper.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
  have hGT : G^2 ≤ 2*T := by
    have h := pow_le_pow_left₀ hG.le hGhi 2
    rw [Real.sq_sqrt hT0.le] at h
    linarith
  have hsmall := hB T ((le_max_right _ _).trans hT) G hlower
  have hcutR : ((m+N:ℕ):ℝ) ≤ atkinsonSourceCutoff T G (Real.log T) := by exact_mod_cast hcut
  exact hblock T G (Real.log T) hT0 hG hGT (Real.log_pos (by linarith)) m N hm (by linarith)

end MathCollab.Density.Stronger.Atkinson
