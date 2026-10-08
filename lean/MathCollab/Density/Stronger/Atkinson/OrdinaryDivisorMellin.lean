module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMellinInversion
public import MathCollab.Density.Stronger.Fourth.SquareSource

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter Topology MeasureTheory
open MathCollab.Density.Stronger.Fourth
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- Actual ordinary-divisor term on the Mellin line. -/
def ordinaryDivisorMellinTerm (g : ℝ → ℂ) (σ : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term divisorWeight ((σ : ℂ) + (u : ℂ) * I) n *
    mellin g ((σ : ℂ) + (u : ℂ) * I)

theorem DFIVoronoiTestFunction.integrable_ordinaryDivisorMellinTerm
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (c : ℝ) (n : ℕ) :
    Integrable (ordinaryDivisorMellinTerm g c n) := by
  unfold ordinaryDivisorMellinTerm
  apply (hg.verticalIntegrable_mellin c).bdd_mul
      (c := ‖LSeries.term divisorWeight (c : ℂ) n‖)
  · by_cases hn : n = 0
    · subst n
      simpa [LSeries.term_zero] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _u : ℝ => (0 : ℂ)))
    · simp_rw [LSeries.term_of_ne_zero hn]
      have hBase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hExponent : Continuous (fun u : ℝ =>
          (c : ℂ) + (u : ℂ) * I) := by fun_prop
      have hPow : Continuous (fun u : ℝ =>
          (n : ℂ) ^ ((c : ℂ) + (u : ℂ) * I)) :=
        hExponent.const_cpow (Or.inl hBase)
      exact (continuous_const.div hPow (fun _u =>
        Complex.cpow_ne_zero_iff.mpr (Or.inl hBase))).aestronglyMeasurable
  · filter_upwards with u
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp

theorem DFIVoronoiTestFunction.integral_norm_ordinaryDivisorMellinTerm
    (g : ℝ → ℂ)
    (c : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖ordinaryDivisorMellinTerm g c n u‖) =
      ‖LSeries.term divisorWeight (c : ℂ) n‖ *
        ∫ u : ℝ, ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖ := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  unfold ordinaryDivisorMellinTerm
  rw [norm_mul]
  congr 1
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

/-- Absolute summability of the norms of all right-line Mellin terms.  This
is the complete Tonelli/Fubini condition used by the Voronoi entry theorem. -/
theorem DFIVoronoiTestFunction.summable_integral_norm_ordinaryDivisorMellinTerm
    (g : ℝ → ℂ)
    {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖ordinaryDivisorMellinTerm g c n u‖) := by
  have hCoeff : LSeriesSummable divisorWeight (c : ℂ) :=
    divisorLSeries_summable (by simpa using hc)
  have hNorm : Summable (fun n : ℕ =>
      ‖LSeries.term divisorWeight (c : ℂ) n‖) :=
    summable_norm_iff.mpr hCoeff
  have hMul := hNorm.mul_right
    (∫ u : ℝ, ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖)
  apply hMul.congr
  intro n
  exact (integral_norm_ordinaryDivisorMellinTerm g c n).symm


theorem divisorWeight_mul_mellinInv
    (g : ℝ → ℂ) (σ : ℝ)
    (n : ℕ) :
    divisorWeight n * mellinInv σ (mellin g) n =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ, ordinaryDivisorMellinTerm g σ n u := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [divisorWeight, ordinaryDivisorMellinTerm, mellinInv,
      LSeries.term_zero]
  · unfold mellinInv ordinaryDivisorMellinTerm
    simp only [smul_eq_mul, Complex.real_smul, ofReal_div, ofReal_one,
      ofReal_mul]
    change divisorWeight n *
        ((1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
          ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) *
            mellin g ((σ : ℂ) + (y : ℂ) * I)) = _
    rw [show divisorWeight n *
        ((1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
          ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) *
            mellin g ((σ : ℂ) + (y : ℂ) * I)) =
        (1 / (2 * Real.pi) : ℂ) * divisorWeight n *
          ∫ y : ℝ, ((n : ℝ) : ℂ) ^
            (-((σ : ℂ) + (y : ℂ) * I)) *
              mellin g ((σ : ℂ) + (y : ℂ) * I) by ring,
      mul_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    funext u
    rw [LSeries.term_of_ne_zero hn]
    rw [show ((n : ℝ) : ℂ) = (n : ℂ) by norm_cast, cpow_neg,
      div_eq_mul_inv]
    ring


/-- Native q=1 right-line identity, with inversion and absolute exchange proved. -/
theorem DFIVoronoiTestFunction.ordinaryDivisorSum_eq_zetaSquareMellinIntegral
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, divisorWeight n * g n) =
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta ((σ : ℂ) + (u : ℂ) * I) ^ 2 *
          mellin g ((σ : ℂ) + (u : ℂ) * I) := by
  have hInvAll : ∀ n : ℕ,
      divisorWeight n * g n = divisorWeight n * mellinInv σ (mellin g) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [divisorWeight]
    · rw [hg.mellinInversion σ (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  simp_rw [hInvAll, divisorWeight_mul_mellinInv]
  rw [tsum_mul_left]
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm
    (hg.integrable_ordinaryDivisorMellinTerm σ)
    (DFIVoronoiTestFunction.summable_integral_norm_ordinaryDivisorMellinTerm g hσ)]
  congr 2
  funext u
  rw [riemannZeta_sq_eq_divisorLSeries (by simpa using hσ)]
  unfold LSeries ordinaryDivisorMellinTerm divisorWeight
  rw [tsum_mul_right]

end MathCollab.Density.Stronger.Atkinson
