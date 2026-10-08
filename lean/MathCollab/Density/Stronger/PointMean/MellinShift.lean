module
-- Reversible module-visibility port of the audited development.
/-
Selected exact two-pole Gamma-zeta-square shifts adapted from Scott McColm,
PointMeanMellinShift.lean and PointMeanContourBasic.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_SHIFT_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
All residues, horizontal limits, vertical integrability and the actual
smoothed divisor identity are proved imports, not theorem hypotheses.
-/
public import MathCollab.Density.Stronger.PointMean.MovingPole
public import MathCollab.Density.Stronger.PointMean.DivisorMellin
public import MathCollab.Density.Stronger.PointMean.MellinHorizontal
public import MathCollab.Density.Stronger.PointMean.MellinVertical

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

def VerticalIntegral (f : ℂ → ℂ) (a : ℝ) : ℂ :=
  I • ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)

def VerticalIntegral' (f : ℂ → ℂ) (a : ℝ) : ℂ :=
  (1 / (2 * Real.pi * I) : ℂ) • VerticalIntegral f a

theorem pintz2023_RectangleIntegral'_eq_edges
    (f : ℂ → ℂ) (a b R : ℝ) :
    RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) =
      HIntegral' f a b (-R) - HIntegral' f a b R +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring
private theorem tendsto_rectangleIntegral'_vertical_sub
    {f : ℂ → ℂ} {a b : ℝ}
    (hBottom : Tendsto (fun R : ℝ => HIntegral' f a b (-R)) atTop (nhds 0))
    (hTop : Tendsto (fun R : ℝ => HIntegral' f a b R) atTop (nhds 0))
    (hIntA : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * I)))
    (hIntB : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * I))) :
    Tendsto (fun R : ℝ =>
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I)) atTop
      (nhds (VerticalIntegral' f b - VerticalIntegral' f a)) := by
  let c : ℂ := (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have hRight : Tendsto (fun R : ℝ =>
      c * ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) atTop
      (nhds (c * ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I))) :=
    (intervalIntegral_tendsto_integral hIntB
      tendsto_neg_atTop_atBot tendsto_id).const_mul c
  have hLeft : Tendsto (fun R : ℝ =>
      c * ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) atTop
      (nhds (c * ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I))) :=
    (intervalIntegral_tendsto_integral hIntA
      tendsto_neg_atTop_atBot tendsto_id).const_mul c
  have hEdges := (hBottom.sub hTop).add (hRight.sub hLeft)
  have hExpanded : Tendsto (fun R : ℝ =>
      HIntegral' f a b (-R) - HIntegral' f a b R +
        ((c * ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
          c * ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I))) atTop
      (nhds (c * (∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I)) -
        c * (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)))) := by
    simpa only [zero_sub, neg_zero, zero_add] using hEdges
  have hRectangle : Tendsto (fun R : ℝ =>
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I)) atTop
      (nhds (c * (∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I)) -
        c * (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)))) := by
    refine hExpanded.congr' ?_
    filter_upwards with R
    rw [pintz2023_RectangleIntegral'_eq_edges]
    dsimp only [c]
    ring
  have hVerticalB : VerticalIntegral' f b =
      c * ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I) := by
    unfold VerticalIntegral' VerticalIntegral
    dsimp only [c]
    simp [smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hVerticalA : VerticalIntegral' f a =
      c * ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I) := by
    unfold VerticalIntegral' VerticalIntegral
    dsimp only [c]
    simp [smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  simpa only [hVerticalB, hVerticalA] using hRectangle

private theorem verticalIntegral'_sub_eq_of_eventual_rectangle
    {f : ℂ → ℂ} {a b : ℝ} {A : ℂ}
    (hBottom : Tendsto (fun R : ℝ => HIntegral' f a b (-R)) atTop (nhds 0))
    (hTop : Tendsto (fun R : ℝ => HIntegral' f a b R) atTop (nhds 0))
    (hIntA : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * I)))
    (hIntB : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * I)))
    (hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) = A) :
    VerticalIntegral' f b - VerticalIntegral' f a = A := by
  have hLimit := tendsto_rectangleIntegral'_vertical_sub
    hBottom hTop hIntA hIntB
  have hConst : Tendsto (fun _R : ℝ => A) atTop (nhds A) := tendsto_const_nhds
  have hLimitA := hConst.congr' (hFinite.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hLimit hLimitA

noncomputable def heathBrownIntermediateLine (delta : ℝ) : ℝ :=
  (1 / 2 - delta) / 2

theorem heathBrown_intermediateLine_pos
    {delta : ℝ} (hdeltaUpper : delta ≤ 1 / 4) :
    0 < heathBrownIntermediateLine delta := by
  unfold heathBrownIntermediateLine
  linarith

theorem heathBrown_intermediateLine_le_quarter
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    heathBrownIntermediateLine delta ≤ 1 / 4 := by
  unfold heathBrownIntermediateLine
  linarith

theorem heathBrown_movingPole_vertical_shift
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s)
          (heathBrownIntermediateLine delta) =
      heathBrownMovingPoleResidue s := by
  let d : ℝ := heathBrownIntermediateLine delta
  let f : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand s
  have hd : 0 < d := heathBrown_intermediateLine_pos hdeltaUpper
  have hdUpper : d ≤ 1 / 4 :=
    heathBrown_intermediateLine_le_quarter hdelta.le
  have hpRe : (heathBrownMovingPole s).re = 1 / 2 - delta := by
    simp [heathBrownMovingPole, hsRe]
    ring
  have hdp : d < (heathBrownMovingPole s).re := by
    rw [hpRe]
    dsimp only [d, heathBrownIntermediateLine]
    linarith
  have hpc : (heathBrownMovingPole s).re < 2 := by rw [hpRe]; linarith
  have hsHalf : 1 / 2 ≤ s.re := by rw [hsRe]; linarith
  have hBottom := tendsto_heathBrownMellin_HIntegral'_neg_zero
    hsHalf (a := d) (b := 2)
    (ha := by dsimp only [d]; linarith)
    (hb := by norm_num) (hab := by linarith)
  have hTop := tendsto_heathBrownMellin_HIntegral'_zero
    hsHalf (a := d) (b := 2)
    (ha := by dsimp only [d]; linarith)
    (hb := by norm_num) (hab := by linarith)
  have hIntD : Integrable (fun u : ℝ =>
      f ((d : ℂ) + (u : ℂ) * I)) := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_plus
      (s := s) (delta := d) hd hdUpper
    · rw [hsRe]
      dsimp only [d, heathBrownIntermediateLine]
      linarith
    · rw [hsRe]
      dsimp only [d, heathBrownIntermediateLine]
      linarith
  have hIntTwo : Integrable (fun u : ℝ =>
      f (((2 : ℝ) : ℂ) + (u : ℂ) * I)) := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_right
    rw [hsRe]
    linarith
  have hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        ((d : ℂ) - (R : ℂ) * I) (((2 : ℝ) : ℂ) + (R : ℂ) * I) =
          heathBrownMovingPoleResidue s := by
    filter_upwards [eventually_gt_atTop
      (max 0 |(heathBrownMovingPole s).im|)] with R hR
    apply heathBrown_movingPole_finite_rectangle hd hdp hpc
    · linarith [le_max_left (0 : ℝ) |(heathBrownMovingPole s).im|]
    · linarith [le_max_right (0 : ℝ) |(heathBrownMovingPole s).im|]
  simpa only [f, d] using verticalIntegral'_sub_eq_of_eventual_rectangle
    hBottom hTop hIntD hIntTwo hFinite

theorem heathBrown_gammaPole_vertical_shift
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s)
        (heathBrownIntermediateLine delta) -
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) =
        riemannZeta s ^ 2 := by
  let d : ℝ := heathBrownIntermediateLine delta
  let f : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand s
  have hd : 0 < d := heathBrown_intermediateLine_pos hdeltaUpper
  have hdUpper : d ≤ 1 / 4 :=
    heathBrown_intermediateLine_le_quarter hdelta.le
  have hpRe : (heathBrownMovingPole s).re = 1 / 2 - delta := by
    simp [heathBrownMovingPole, hsRe]
    ring
  have hdp : d < (heathBrownMovingPole s).re := by
    rw [hpRe]
    dsimp only [d, heathBrownIntermediateLine]
    linarith
  have hsHalf : 1 / 2 ≤ s.re := by rw [hsRe]; linarith
  have hBottom := tendsto_heathBrownMellin_HIntegral'_neg_zero
    hsHalf (a := -delta) (b := d)
    (ha := by linarith)
    (hb := by dsimp only [d, heathBrownIntermediateLine]; linarith)
    (hab := by linarith)
  have hTop := tendsto_heathBrownMellin_HIntegral'_zero
    hsHalf (a := -delta) (b := d)
    (ha := by linarith)
    (hb := by dsimp only [d, heathBrownIntermediateLine]; linarith)
    (hab := by linarith)
  have hIntMinus : Integrable (fun u : ℝ =>
      f (((-delta : ℝ) : ℂ) + (u : ℂ) * I)) := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_minus
      (s := s) hdelta hdeltaUpper
    · rw [hsRe]
      norm_num
    · rw [hsRe]
      linarith
  have hIntD : Integrable (fun u : ℝ =>
      f ((d : ℂ) + (u : ℂ) * I)) := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_plus
      (s := s) (delta := d) hd hdUpper
    · rw [hsRe]
      dsimp only [d, heathBrownIntermediateLine]
      linarith
    · rw [hsRe]
      dsimp only [d, heathBrownIntermediateLine]
      linarith
  have hFinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f
        (((-delta : ℝ) : ℂ) - (R : ℂ) * I)
        ((d : ℂ) + (R : ℂ) * I) = riemannZeta s ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [show (((-delta : ℝ) : ℂ)) = (-delta : ℂ) by norm_num]
    exact heathBrown_gammaPole_finite_rectangle
      (s := s) hdelta (by linarith) hd hdp hR
  simpa only [f, d] using verticalIntegral'_sub_eq_of_eventual_rectangle
    hBottom hTop hIntMinus hIntD hFinite

/-- Exact completed form of the two residue shifts. -/
theorem heathBrown_twoPole_vertical_shift
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 -
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) =
        heathBrownMovingPoleResidue s + riemannZeta s ^ 2 := by
  have hMoving := heathBrown_movingPole_vertical_shift
    hdelta hdeltaUpper hsRe
  have hGamma := heathBrown_gammaPole_vertical_shift
    hdelta hdeltaUpper hsRe
  linear_combination hMoving + hGamma

theorem heathBrownSmoothedDivisorSeries_eq_rightVertical
    {s : ℂ} (hs : 0 < s.re) :
    heathBrownSmoothedDivisorSeries s =
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 := by
  rw [heathBrown_smoothed_divisor_eq_right_mellin hs]
  unfold VerticalIntegral' VerticalIntegral heathBrownDivisorMellinIntegrand
  simp [heathBrownZetaSquareMellinIntegrand, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  simp only [mul_comm I]
  ring

/-- Heath--Brown's exact zeta-square identity before estimating the retained
critical-line contour and the two harmless terms. -/
theorem heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    riemannZeta s ^ 2 =
      heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) := by
  have hShift := heathBrown_twoPole_vertical_shift
    hdelta hdeltaUpper hsRe
  have hRight := heathBrownSmoothedDivisorSeries_eq_rightVertical
    (s := s) (by rw [hsRe]; linarith)
  rw [← hRight] at hShift
  calc
    riemannZeta s ^ 2 =
        (heathBrownSmoothedDivisorSeries s -
          VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)) -
            heathBrownMovingPoleResidue s := by
      rw [hShift]
      ring
    _ = heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) := by
      ring

end MathCollab.Density.Stronger.PointMean
