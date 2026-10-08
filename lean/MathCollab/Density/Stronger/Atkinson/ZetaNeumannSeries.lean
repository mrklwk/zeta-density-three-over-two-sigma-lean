module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected ZetaNeumannSeries.lean proofs,
revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
The complete original Y0 series is proved absolutely convergent using the native
q=1 Voronoi transform, then the actual summable remainder is subtracted.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonVoronoi
public import MathCollab.Density.Stronger.Atkinson.NeumannRemainderSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonTwoTermSum (T G L : ℝ) : ℂ := ∑' n : ℕ, zetaAtkinsonTwoTerm T G L n

theorem zetaAtkinsonY0Term_eq_native {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (n : ℕ) :
    zetaAtkinsonY0Term T G L n =
      divisorWeight n * dfiVoronoiMinusTransform 1 (mellin (zetaAtkinsonDivisorTest T G L)) n := by
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonY0Term, divisorWeight]
  have h := dfiVoronoiMinusTransform_mellin_eq_bessel 1 n (Nat.pos_of_ne_zero hn)
    (zetaAtkinsonDivisorVoronoiTest hT hG hL)
  change dfiVoronoiMinusTransform 1 (mellin (zetaAtkinsonDivisorTest T G L)) n = _ at h
  rw [h]
  simp only [zetaAtkinsonY0Term, zetaAtkinsonY0Integrand, dfiVoronoiMinusBesselTransform,
    Nat.cast_one, div_one, mul_assoc]

theorem summable_zetaAtkinsonY0Term {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    Summable (zetaAtkinsonY0Term T G L) := by
  have h := (zetaAtkinsonDivisorVoronoiTest hT hG hL).summable_divisorWeight_voronoiMinus
  apply h.congr
  intro n
  exact (zetaAtkinsonY0Term_eq_native hT hG hL n).symm

theorem summable_zetaAtkinsonTwoTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (zetaAtkinsonTwoTerm T G L) := by
  have h := (summable_zetaAtkinsonY0Term (T := T) (by linarith) hG hL).sub
    (summable_zetaNeumannRemainderTerm hT hG hGT hL hwidth)
  exact h.congr (fun n => (zetaAtkinsonTwoTerm_eq_sub hT hG hL hwidth n).symm)

theorem zetaAtkinsonBesselMinus_sub_twoTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    zetaAtkinsonBesselMinus T G L - zetaAtkinsonTwoTermSum T G L =
      ∑' n : ℕ, zetaNeumannRemainderTerm T G L n := by
  unfold zetaAtkinsonTwoTermSum
  simp_rw [zetaAtkinsonTwoTerm_eq_sub hT hG hL hwidth]
  rw [(summable_zetaAtkinsonY0Term (T := T) (by linarith) hG hL).tsum_sub
    (summable_zetaNeumannRemainderTerm hT hG hGT hL hwidth)]
  change (∑' n : ℕ, zetaAtkinsonY0Term T G L n) -
    ((∑' n : ℕ, zetaAtkinsonY0Term T G L n) - ∑' n : ℕ, zetaNeumannRemainderTerm T G L n) = _
  ring

theorem exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
        ‖zetaAtkinsonBesselMinus T G L - zetaAtkinsonTwoTermSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_tsum_zetaNeumannRemainderTerm_le
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  rw [zetaAtkinsonBesselMinus_sub_twoTerm hT hG hGT hL hwidth]
  exact hbound T G L hT hG hGT hL hwidth

end MathCollab.Density.Stronger.Atkinson
