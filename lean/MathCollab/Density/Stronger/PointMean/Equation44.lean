module
-- Reversible module-visibility port of the audited development.
/-
Selected finite exponential-overlap/point-mean consumer proofs adapted from
Scott McColm, PointMeanEquation44.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The repository's literal actual-zeta norm and oneSeparated predicate are used.
-/
public import MathCollab.Density.Stronger.PointMean.Native
public import MathCollab.Density.Stronger.PointMean.IntegralOverlap

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Finset MeasureTheory
open scoped BigOperators Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The complete source equation-(44) inequality, with its absolute constant
inherited from Lemma 3. -/
theorem heathBrown_equation44_of_lemmaThree
    (hLemmaThree : HeathBrownLemmaThree) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T V center G L : ℝ) (W : Finset ℝ),
        10 ≤ T → 0 < V → 0 ≤ G → 0 ≤ L →
        oneSeparated W →
        (∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2) →
        10 ≤ center - G / 2 → center + G / 2 ≤ T →
        (∀ t ∈ W, Real.log t ^ (2 : ℕ) ≤ L) →
        G / 2 + L ≤ G →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        V ^ (2 : ℕ) * (W.card : ℝ) ≤
          C * Real.log T *
            ((W.card : ℝ) + 4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ))) := by
  obtain ⟨C, hC, hpoint⟩ := hLemmaThree
  refine ⟨C, hC, ?_⟩
  intro T V center G L W hT hV hG hL hSep hRange hLow hHigh
    hLogRadius hFit hLarge
  let q : ℝ → ℝ := fun t ↦
    ∫ u in t - L..t + L,
      Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)
  have hPer : ∀ t ∈ W,
      V ^ (2 : ℕ) ≤ C * Real.log T * (1 + q t) := by
    intro t ht
    have htRange := hRange t ht
    have htTen : 10 ≤ t := by linarith
    have htT : t ≤ T := by linarith
    have htPos : 0 < t := lt_of_lt_of_le (by norm_num) htTen
    have hTPos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hlogMono : Real.log t ≤ Real.log T := Real.log_le_log htPos htT
    have hqNonneg : 0 ≤ q t := by
      dsimp [q]
      exact intervalIntegral.integral_nonneg (by linarith) fun u hu ↦ by
        positivity
    have hMoment := heathBrownLemmaThreeMoment_le_centered t L
      (hLogRadius t ht)
    have hSource := hpoint t htTen
    have hVzeta : V ^ (2 : ℕ) ≤
        zetaMomentCriticalNorm t ^ (2 : ℕ) := by
      nlinarith [hLarge t ht, sq_nonneg V,
        sq_nonneg (zetaMomentCriticalNorm t)]
    calc
      V ^ (2 : ℕ) ≤ zetaMomentCriticalNorm t ^ (2 : ℕ) := hVzeta
      _ ≤ C * Real.log t *
          (1 + heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ))) := hSource
      _ ≤ C * Real.log t * (1 + q t) := by
        exact mul_le_mul_of_nonneg_left (add_le_add_right hMoment 1)
          (mul_nonneg hC.le hlogt)
      _ ≤ C * Real.log T * (1 + q t) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogMono hC.le) (by linarith)
  have hSummed :
      ∑ t ∈ W, V ^ (2 : ℕ) ≤
        ∑ t ∈ W, C * Real.log T * (1 + q t) :=
    Finset.sum_le_sum fun t ht ↦ hPer t ht
  have hOverlap : ∑ t ∈ W, q t ≤
      4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ)) := by
    exact sum_truncated_exp_kernel_zeta_sq_le_localSecondMoment
      W center G L hG hL hRange hFit hSep
  have hCoeff : 0 ≤ C * Real.log T := by
    exact mul_nonneg hC.le (Real.log_nonneg (by linarith))
  calc
    V ^ (2 : ℕ) * (W.card : ℝ) = ∑ t ∈ W, V ^ (2 : ℕ) := by
      simp [mul_comm]
    _ ≤ ∑ t ∈ W, C * Real.log T * (1 + q t) := hSummed
    _ = C * Real.log T * ((W.card : ℝ) + ∑ t ∈ W, q t) := by
      simp only [mul_add, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ C * Real.log T *
        ((W.card : ℝ) + 4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right hOverlap (W.card : ℝ)) hCoeff


/-- Heath--Brown (1978), equation (44), obtained from the proved contour,
tail, and compact-range versions of Lemma 3. -/
theorem heathBrown_equation44_native :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T V center G L : ℝ) (W : Finset ℝ),
        10 ≤ T → 0 < V → 0 ≤ G → 0 ≤ L →
        oneSeparated W →
        (∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2) →
        10 ≤ center - G / 2 → center + G / 2 ≤ T →
        (∀ t ∈ W, Real.log t ^ (2 : ℕ) ≤ L) →
        G / 2 + L ≤ G →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        V ^ (2 : ℕ) * (W.card : ℝ) ≤
          C * Real.log T *
            ((W.card : ℝ) + 4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ))) :=
  heathBrown_equation44_of_lemmaThree heathBrownLemmaThree_native

end MathCollab.Density.Stronger.PointMean
