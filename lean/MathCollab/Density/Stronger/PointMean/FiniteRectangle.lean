module
-- Reversible module-visibility port of the audited development.
/-
Selected native Heath--Brown point-mean contour proofs adapted from
Scott McColm, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
PointMeanGammaPole.lean and PointMeanLemmaThreeContour.lean.
MIT-0, Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_RECTANGLE_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local imported rectangle residue machinery retains its Apache-2.0 attribution.
No source project module is imported; no point-mean or moment bound is assumed.
-/
public import MathCollab.Density.RectangleResidue
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter
open MathCollab.Density.Contour
open scoped Topology Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The literal Gamma--zeta-square Mellin kernel of the native point-mean proof. -/
def heathBrownZetaSquareMellinIntegrand (s w : ℂ) : ℂ :=
  Complex.Gamma w * riemannZeta (s + w) ^ 2

/-- Holomorphic numerator which clears Gamma's simple pole at zero. -/
noncomputable def heathBrownGammaPoleNumerator (s w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * riemannZeta (s + w) ^ 2

theorem heathBrownGammaPoleNumerator_zero (s : ℂ) :
    heathBrownGammaPoleNumerator s 0 = riemannZeta s ^ 2 := by
  simp [heathBrownGammaPoleNumerator]

theorem heathBrownZetaSquareMellinIntegrand_eq_gammaPoleCleared
    {s w : ℂ} (hw : w ≠ 0) :
    heathBrownZetaSquareMellinIntegrand s w =
      heathBrownGammaPoleNumerator s w / w := by
  have hRec := Complex.Gamma_add_one w hw
  unfold heathBrownZetaSquareMellinIntegrand heathBrownGammaPoleNumerator
  rw [hRec]
  field_simp [hw]

/-- Finite shift across Gamma's pole.  The condition `d < Re(1-s)` keeps the
moving zeta pole strictly to the right of this rectangle. -/
theorem heathBrown_gammaPole_finite_rectangle
    {s : ℂ} {delta d H : ℝ}
    (hdelta : 0 < delta) (hdeltaUpper : delta < 1)
    (hd : 0 < d) (hdp : d < (1 - s).re)
    (hH : 0 < H) :
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        ((-delta : ℂ) - (H : ℂ) * I) ((d : ℂ) + (H : ℂ) * I) =
      riemannZeta s ^ 2 := by
  let z : ℂ := (-delta : ℂ) - (H : ℂ) * I
  let w : ℂ := (d : ℂ) + (H : ℂ) * I
  let F : ℂ → ℂ := heathBrownGammaPoleNumerator s
  have hzre : z.re ≤ w.re := by simp [z, w]; linarith
  have hzim : z.im ≤ w.im := by simp [z, w]; linarith
  have hzero : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hzre, uIoo_of_le hzim,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    simp [z, w, hdelta, hd, hH]
  have hF : DifferentiableOn ℂ F (Rectangle z w) := by
    intro u hu
    have huBounds := (mem_Rect hzre hzim u).mp hu
    have huLower : -delta ≤ u.re := by
      have hzReal : z.re = -delta := by simp [z]
      linarith [huBounds.1]
    have huUpper : u.re ≤ d := by
      have hwReal : w.re = d := by simp [w]
      linarith [huBounds.2.1]
    have huNegOne : -(1 : ℝ) < u.re := by linarith
    have hGamma : DifferentiableAt ℂ
        (fun v : ℂ => Complex.Gamma (v + 1)) u := by
      apply (Complex.differentiableAt_Gamma (u + 1) ?_).comp u
        (differentiableAt_id.add_const 1)
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      linarith
    have hNotPole : s + u ≠ 1 := by
      intro hsu
      have hre := congrArg Complex.re hsu
      have hpRe : (1 - s).re = 1 - s.re := by
        simp
      simp only [add_re, one_re] at hre
      linarith
    have hZeta : DifferentiableAt ℂ
        (fun v : ℂ => riemannZeta (s + v)) u :=
      (differentiableAt_riemannZeta hNotPole).comp u
        (differentiableAt_const (c := s) |>.add differentiableAt_id)
    exact (hGamma.mul (hZeta.pow 2)).differentiableWithinAt
  have hSlope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    exact (Complex.differentiableOn_dslope hzero).2 hF
  have hPrincipal : Set.EqOn
      ((fun u : ℂ => F u / u) - fun u => F 0 / (u - 0))
      (dslope F 0) (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    rw [Pi.sub_apply, dslope_of_ne F hu0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp [hu0]
  have hCleared := ResidueTheoremOnRectangleWithSimplePole
    (f := fun u : ℂ => F u / u) (g := dslope F 0)
    (p := 0) (A := F 0) hzre hzim hzero hSlope hPrincipal
  have hzeroNotBorder : (0 : ℂ) ∉ RectangleBorder z w :=
    not_mem_rectangleBorder_of_rectangle_mem_nhds hzero
  have hCongr : Set.EqOn
      (heathBrownZetaSquareMellinIntegrand s)
      (fun u : ℂ => F u / u) (RectangleBorder z w) := by
    intro u hu
    have hu0 : u ≠ 0 := fun h => hzeroNotBorder (h ▸ hu)
    simpa only [F] using
      heathBrownZetaSquareMellinIntegrand_eq_gammaPoleCleared
        (s := s) hu0
  rw [RectangleIntegral'_congr hCongr]
  simpa only [F, heathBrownGammaPoleNumerator_zero] using hCleared


private theorem exp_two_le_eight_heathBrown : Real.exp 2 ≤ 8 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

theorem two_lt_log_of_ten_le {t : ℝ} (ht : 10 ≤ t) :
    2 < Real.log t := by
  rw [Real.lt_log_iff_exp_lt (by linarith : 0 < t)]
  exact exp_two_le_eight_heathBrown.trans_lt (by linarith)

/-- Source parameters used by the Lemma-3 residue rectangle. -/
noncomputable def heathBrownLemmaThreeDelta (t : ℝ) : ℝ :=
  1 / Real.log t

noncomputable def heathBrownLemmaThreeRadius (t : ℝ) : ℝ :=
  Real.log t ^ (2 : ℕ)

theorem heathBrownLemmaThreeDelta_pos {t : ℝ} (ht : 10 ≤ t) :
    0 < heathBrownLemmaThreeDelta t := by
  unfold heathBrownLemmaThreeDelta
  have := two_lt_log_of_ten_le ht
  positivity

theorem heathBrownLemmaThreeDelta_lt_half {t : ℝ} (ht : 10 ≤ t) :
    heathBrownLemmaThreeDelta t < 1 / 2 := by
  unfold heathBrownLemmaThreeDelta
  exact one_div_lt_one_div_of_lt (by norm_num) (two_lt_log_of_ten_le ht)

theorem heathBrownLemmaThreeRadius_pos {t : ℝ} (ht : 10 ≤ t) :
    0 < heathBrownLemmaThreeRadius t := by
  unfold heathBrownLemmaThreeRadius
  exact sq_pos_of_pos (by linarith [two_lt_log_of_ten_le ht])

/-- The exact residue identity used in the proof of Heath--Brown Lemma 3. -/
theorem heathBrownLemmaThree_finiteRectangle (t : ℝ) (ht : 10 ≤ t) :
    RectangleIntegral'
        (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        (((-heathBrownLemmaThreeDelta t : ℝ) : ℂ) -
          (heathBrownLemmaThreeRadius t : ℂ) * I)
        (((heathBrownLemmaThreeDelta t : ℝ) : ℂ) +
          (heathBrownLemmaThreeRadius t : ℂ) * I) =
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ 2 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  let delta : ℝ := heathBrownLemmaThreeDelta t
  let H : ℝ := heathBrownLemmaThreeRadius t
  have hdelta : 0 < delta := heathBrownLemmaThreeDelta_pos ht
  have hdeltaHalf : delta < 1 / 2 := heathBrownLemmaThreeDelta_lt_half ht
  have hH : 0 < H := heathBrownLemmaThreeRadius_pos ht
  have hpRe : (1 - s).re = 1 / 2 := by
    simp [s]
    ring
  have hrect := heathBrown_gammaPole_finite_rectangle
    (s := s) (delta := delta) (d := delta) (H := H)
    hdelta (hdeltaHalf.trans (by norm_num)) hdelta
    (by rw [hpRe]; exact hdeltaHalf) hH
  simpa only [s, delta, H, ofReal_neg] using hrect

/-- Expansion of the normalized source rectangle into its two horizontal
and two vertical edges, retaining their orientations. -/
theorem heathBrownLemmaThree_rectangle_eq_edges (t : ℝ) :
    let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
    let delta : ℝ := heathBrownLemmaThreeDelta t
    let H : ℝ := heathBrownLemmaThreeRadius t
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        (((-delta : ℝ) : ℂ) - (H : ℂ) * I)
        (((delta : ℝ) : ℂ) + (H : ℂ) * I) =
      HIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) delta (-H) -
        HIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) delta H +
        VIntegral' (heathBrownZetaSquareMellinIntegrand s) delta (-H) H -
        VIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) (-H) H := by
  dsimp only
  unfold RectangleIntegral' RectangleIntegral HIntegral' VIntegral'
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
  ring


end MathCollab.Density.Stronger.PointMean
