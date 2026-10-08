module
-- Reversible module-visibility port of the audited development.
/-
Selected moving-pole proofs from Scott McColm, PointMeanMovingPole.lean,
exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_SHIFT_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The pole-removed zeta function is built from local AbelZetaGrowth.
-/
public import MathCollab.Density.Stronger.PointMean.DoublePole
public import MathCollab.Density.Stronger.PointMean.FiniteRectangle
public import MathCollab.Density.Stronger.Fourth.GammaShiftLog
public import MathCollab.Density.AbelZetaGrowth

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
open MathCollab.Density.Contour MathCollab.Density.ZetaGrowth
open MathCollab.Density.Stronger.Fourth
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- Entire continuation of u*zeta(1+u), normalized to one at zero. -/
def riemannZetaPoleRemoved (u : ℂ) : ℂ := regularizedRiemannZeta (1 + u)

theorem riemannZetaPoleRemoved_zero : riemannZetaPoleRemoved 0 = 1 := by
  simp [riemannZetaPoleRemoved, regularizedRiemannZeta]

theorem riemannZetaPoleRemoved_eq_mul_riemannZeta {u : ℂ} (hu : u ≠ 0) :
    riemannZetaPoleRemoved u = u * riemannZeta (1 + u) := by
  have h : 1 + u ≠ 1 := by simpa using hu
  simp [riemannZetaPoleRemoved, regularizedRiemannZeta, Function.update_of_ne h]

theorem differentiable_riemannZetaPoleRemoved : Differentiable ℂ riemannZetaPoleRemoved := by
  intro u
  exact (differentiableAt_regularizedRiemannZeta (1 + u)).comp u
    (differentiableAt_const (c := (1 : ℂ)) |>.add differentiableAt_id)

noncomputable def heathBrownMovingPole (s : ℂ) : ℂ := 1 - s

/-- Holomorphic numerator obtained by clearing the moving double zeta pole. -/
noncomputable def heathBrownMovingPoleNumerator (s w : ℂ) : ℂ :=
  Complex.Gamma w *
    riemannZetaPoleRemoved (w - heathBrownMovingPole s) ^ 2

theorem heathBrownMovingPoleNumerator_at_pole (s : ℂ) :
    heathBrownMovingPoleNumerator s (heathBrownMovingPole s) =
      Complex.Gamma (heathBrownMovingPole s) := by
  simp [heathBrownMovingPoleNumerator, riemannZetaPoleRemoved_zero]

/-- Away from `1-s`, the source integrand is exactly the pole-cleared
numerator divided by the squared Cauchy kernel. -/
theorem heathBrownZetaSquareMellinIntegrand_eq_poleCleared
    {s w : ℂ} (hw : w ≠ heathBrownMovingPole s) :
    heathBrownZetaSquareMellinIntegrand s w =
      heathBrownMovingPoleNumerator s w /
        (w - heathBrownMovingPole s) ^ 2 := by
  let p : ℂ := heathBrownMovingPole s
  let u : ℂ := w - p
  have hu : u ≠ 0 := sub_ne_zero.mpr hw
  have haffine : s + w = 1 + u := by
    dsimp only [u, p, heathBrownMovingPole]
    ring
  have hpole := riemannZetaPoleRemoved_eq_mul_riemannZeta hu
  unfold heathBrownZetaSquareMellinIntegrand heathBrownMovingPoleNumerator
  rw [haffine]
  change Complex.Gamma w * riemannZeta (1 + u) ^ 2 =
    Complex.Gamma w * riemannZetaPoleRemoved u ^ 2 / u ^ 2
  rw [hpole]
  field_simp [hu]

theorem differentiableOn_heathBrownMovingPoleNumerator
    (s : ℂ) :
    DifferentiableOn ℂ (heathBrownMovingPoleNumerator s)
      {w : ℂ | 0 < w.re} := by
  intro w hw
  have hGamma : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    change 0 < w.re at hw
    linarith
  have hRemoved : DifferentiableAt ℂ
      (fun z : ℂ => riemannZetaPoleRemoved
        (z - heathBrownMovingPole s)) w :=
    differentiable_riemannZetaPoleRemoved.differentiableAt.comp w (by fun_prop)
  exact (hGamma.mul (hRemoved.pow 2)).differentiableWithinAt

/-- Exact coefficient of the order-one term created by the moving double
pole.  This is the residue which must later be bounded uniformly. -/
noncomputable def heathBrownMovingPoleResidue (s : ℂ) : ℂ :=
  deriv (heathBrownMovingPoleNumerator s) (heathBrownMovingPole s)

/-- Explicit Gamma--digamma form of the moving residue. -/
theorem heathBrownMovingPoleResidue_eq
    {s : ℂ} (hp : 0 < (heathBrownMovingPole s).re) :
    heathBrownMovingPoleResidue s =
      Complex.Gamma (heathBrownMovingPole s) *
          Complex.digamma (heathBrownMovingPole s) +
        2 * Complex.Gamma (heathBrownMovingPole s) *
          deriv riemannZetaPoleRemoved 0 := by
  let p : ℂ := heathBrownMovingPole s
  have hGamma := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hp
  have hRemoved0 : HasDerivAt riemannZetaPoleRemoved
      (deriv riemannZetaPoleRemoved 0) 0 :=
    differentiable_riemannZetaPoleRemoved.differentiableAt.hasDerivAt
  have hAffine : HasDerivAt (fun w : ℂ => w - p) 1 p := by
    simpa only [id_eq] using
      (HasDerivAt.sub_const p (hasDerivAt_id p))
  have hRemovedAt : HasDerivAt riemannZetaPoleRemoved
      (deriv riemannZetaPoleRemoved 0) (p - p) := by
    simpa using hRemoved0
  have hRemoved : HasDerivAt
      (fun w : ℂ => riemannZetaPoleRemoved (w - p))
      (deriv riemannZetaPoleRemoved 0) p := by
    simpa only [Function.comp_apply, mul_one] using!
      HasDerivAt.comp (h := fun w : ℂ => w - p)
        (h₂ := riemannZetaPoleRemoved) p hRemovedAt hAffine
  have hProduct := hGamma.mul (hRemoved.pow 2)
  unfold heathBrownMovingPoleResidue heathBrownMovingPoleNumerator
  change deriv
      (fun w : ℂ => Complex.Gamma w * riemannZetaPoleRemoved (w - p) ^ 2) p =
    Complex.Gamma p * Complex.digamma p +
      2 * Complex.Gamma p * deriv riemannZetaPoleRemoved 0
  calc
    deriv
        (fun w : ℂ => Complex.Gamma w *
          riemannZetaPoleRemoved (w - p) ^ 2) p =
      Complex.Gamma p * Complex.digamma p *
          riemannZetaPoleRemoved (p - p) ^ 2 +
        Complex.Gamma p *
          ((2 : ℂ) * riemannZetaPoleRemoved (p - p) ^ (2 - 1) *
            deriv riemannZetaPoleRemoved 0) := by
      simpa only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat] using! hProduct.deriv
    _ = Complex.Gamma p * Complex.digamma p +
        2 * Complex.Gamma p * deriv riemannZetaPoleRemoved 0 := by
      rw [sub_self, riemannZetaPoleRemoved_zero]
      norm_num
      ring

/-- The finite contour shift from `Re w = c` to a positive line `Re w = d`.
Only the moving double zeta pole is crossed; Gamma's pole at zero remains to
the left. -/
theorem heathBrown_movingPole_finite_rectangle
    {s : ℂ} {d c H : ℝ}
    (hd : 0 < d)
    (hdp : d < (heathBrownMovingPole s).re)
    (hpc : (heathBrownMovingPole s).re < c)
    (hH : 0 < H)
    (hpH : |(heathBrownMovingPole s).im| < H) :
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        ((d : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      heathBrownMovingPoleResidue s := by
  let z : ℂ := (d : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  let p : ℂ := heathBrownMovingPole s
  let N : ℂ → ℂ := heathBrownMovingPoleNumerator s
  have hzre : z.re ≤ w.re := by
    simp [z, w]
    linarith
  have hzim : z.im ≤ w.im := by simp [z, w]; linarith
  have hpInterior : Rectangle z w ∈ 𝓝 p := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hzre, uIoo_of_le hzim,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · simp [z, w, p]
      exact ⟨hdp, hpc⟩
    · simp [z, w]
      exact (abs_lt.mp hpH)
  have hRectPositive : Rectangle z w ⊆ {u : ℂ | 0 < u.re} := by
    intro u hu
    have huBounds := (mem_Rect hzre hzim u).mp hu
    change 0 < u.re
    have hzReal : z.re = d := by simp [z]
    linarith [huBounds.1]
  have hN : DifferentiableOn ℂ N (Rectangle z w) :=
    (differentiableOn_heathBrownMovingPoleNumerator s).mono hRectPositive
  have hPoleCleared := rectangleIntegral'_div_sq_eq_deriv
    hzre hzim hpInterior hN
  have hpNotBorder : p ∉ RectangleBorder z w :=
    not_mem_rectangleBorder_of_rectangle_mem_nhds hpInterior
  have hCongr : Set.EqOn
      (heathBrownZetaSquareMellinIntegrand s)
      (fun u : ℂ => N u / (u - p) ^ 2) (RectangleBorder z w) := by
    intro u hu
    have hup : u ≠ p := fun h => hpNotBorder (h ▸ hu)
    simpa only [N, p] using
      heathBrownZetaSquareMellinIntegrand_eq_poleCleared hup
  rw [RectangleIntegral'_congr hCongr]
  simpa only [N, p, heathBrownMovingPoleResidue] using hPoleCleared

end MathCollab.Density.Stronger.PointMean
