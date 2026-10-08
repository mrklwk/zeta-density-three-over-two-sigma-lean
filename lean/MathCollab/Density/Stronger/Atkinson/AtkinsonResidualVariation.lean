module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCompactProfiles
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSampleGeometry

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSaddleResidual (T G L b : ℝ) : ℂ :=
  zetaMainMellinProfile (zetaAtkinsonSaddle T b / T) *
    (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ)

theorem zetaMainMellinProfile_saddle_eq_root {T : ℝ} (hT : 0 < T) (b : ℝ) :
    zetaMainMellinProfile (zetaAtkinsonSaddle T b/T) =
      atkinsonPowerProfile 0 ((atkinsonSaddleRoot (T/(2*Real.pi)) b/Real.sqrt T)^2) := by
  unfold atkinsonPowerProfile zetaAtkinsonSaddle
  rw [div_pow,Real.sq_sqrt hT.le]
  simp only [neg_zero,Real.rpow_zero,Complex.ofReal_one,one_mul]

theorem exists_finiteVariationBound_saddleMellin :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ m N : ℕ,
      10000*((m+N:ℕ):ℝ) ≤ T →
      FiniteVariationBound (fun i => zetaMainMellinProfile
        (zetaAtkinsonSaddle T (Real.sqrt ((m+i:ℕ):ℝ))/T)) N C ∧
      FiniteVariationBound (fun i => zetaMainMellinProfile
        (zetaAtkinsonSaddle T (-Real.sqrt ((m+i:ℕ):ℝ))/T)) N C := by
  obtain ⟨C,hC,hprofile⟩ := exists_intervalC2Bound_atkinsonPowerRootProfile 0
  refine ⟨C,hC,?_⟩
  intro T hT m N hN
  have hbound (u : ℕ → ℝ) (hm : MonotoneOn u (Iic N) ∨ AntitoneOn u (Iic N))
      (hr : ∀ i ≤ N, u i ∈ Icc (1/4) 1) :
      FiniteVariationBound (fun i => atkinsonPowerProfile 0 ((u i)^2)) N C := by
    apply finiteVariationBound_comp_of_lipschitz hC.le (by norm_num) hm hr hprofile.norm_le
    intro x hx y hy
    simpa only [mul_one] using hprofile.norm_sub_le hx hy
  constructor
  · apply (hbound _ (Or.inl ((atkinsonPositiveRootSample_monotone hT m).monotoneOn (Iic N)))
      (fun i hi => (atkinsonRootSample_mem hT m N hN i hi).1)).congr
    intro i _
    exact zetaMainMellinProfile_saddle_eq_root hT _
  · apply (hbound _ (Or.inr ((atkinsonNegativeRootSample_antitone hT m).antitoneOn (Iic N)))
      (fun i hi => (atkinsonRootSample_mem hT m N hN i hi).2)).congr
    intro i _
    exact zetaMainMellinProfile_saddle_eq_root hT _

theorem finiteVariationBound_saddleCutoff {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (m N : ℕ) :
    FiniteVariationBound (fun i => (zetaDivisorBandCutoff T G L
      (zetaAtkinsonSaddle T (Real.sqrt ((m+i:ℕ):ℝ))) : ℂ)) N 2 ∧
    FiniteVariationBound (fun i => (zetaDivisorBandCutoff T G L
      (zetaAtkinsonSaddle T (-Real.sqrt ((m+i:ℕ):ℝ))) : ℂ)) N 2 := by
  have he := zetaDivisorBandEdge_strictMono hT hG
  have hp : Monotone (fun i : ℕ => zetaAtkinsonSaddle T (Real.sqrt ((m+i:ℕ):ℝ))) := by
    intro i j hij
    apply zetaAtkinsonSaddle_monotone hT
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)
  have hm : Antitone (fun i : ℕ => zetaAtkinsonSaddle T (-Real.sqrt ((m+i:ℕ):ℝ))) := by
    intro i j hij
    apply zetaAtkinsonSaddle_monotone hT
    apply neg_le_neg
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)
  exact ⟨finiteVariationBound_zetaBandCutoff_sample (he (by linarith)) (he (by linarith))
    _ N (Or.inl (hp.monotoneOn (Iic N))),
    finiteVariationBound_zetaBandCutoff_sample (he (by linarith)) (he (by linarith))
    _ N (Or.inr (hm.antitoneOn (Iic N)))⟩

theorem exists_finiteVariationBound_saddleResidual :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → 0 < L →
      ∀ m N : ℕ, 10000*((m+N:ℕ):ℝ) ≤ T →
      FiniteVariationBound (fun i => atkinsonSaddleResidual T G L (Real.sqrt ((m+i:ℕ):ℝ))) N C ∧
      FiniteVariationBound (fun i => atkinsonSaddleResidual T G L (-Real.sqrt ((m+i:ℕ):ℝ))) N C := by
  obtain ⟨C,hC,hM⟩ := exists_finiteVariationBound_saddleMellin
  refine ⟨4*C,by positivity,?_⟩
  intro T G L hT hG hL m N hN
  obtain ⟨hp,hm⟩ := hM T hT m N hN
  obtain ⟨hpc,hmc⟩ := finiteVariationBound_saddleCutoff hT hG hL m N
  constructor
  · convert hp.mul hpc using 1
    · rfl
    · ring
  · convert hm.mul hmc using 1
    · rfl
    · ring

end MathCollab.Density.Stronger.Atkinson
