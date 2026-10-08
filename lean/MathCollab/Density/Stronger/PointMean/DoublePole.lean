module
-- Reversible module-visibility port of the audited development.
/-
Selected double-pole rectangle proofs from Scott McColm, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1: DivisorVoronoi.lean and
PointMeanDoublePole.lean. MIT-0, Copyright 2026 S. McColm.
Local RectangleResidue retains its Apache-2.0 attribution.
See SOURCE-MANIFEST.json and LICENSE-MIT-0; no upstream module is imported.
-/
public import MathCollab.Density.RectangleResidue
public import Mathlib.Analysis.Complex.RealDeriv

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open MathCollab.Density.Contour
open scoped Topology Interval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

private theorem hasDerivAt_ofReal (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
  simpa using! (Complex.ofRealCLM.hasDerivAt (x := x))

private theorem hIntegral_const_div_sq (C p : ℂ) (x₁ x₂ y : ℝ)
    (hy : y ≠ p.im) :
    HIntegral (fun s : ℂ => C / (s - p) ^ 2) x₁ x₂ y =
      -C / ((x₂ : ℂ) + (y : ℂ) * I - p) -
        (-C / ((x₁ : ℂ) + (y : ℂ) * I - p)) := by
  let F : ℝ → ℂ := fun x => -C / ((x : ℂ) + (y : ℂ) * I - p)
  let F' : ℝ → ℂ := fun x => C / ((x : ℂ) + (y : ℂ) * I - p) ^ 2
  have hne : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I - p) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp only [sub_im, add_im, ofReal_im, ofReal_re, mul_im, I_im, I_re,
      mul_one, mul_zero, zero_add, zero_im, add_zero] at hi
    exact hy (sub_eq_zero.mp hi)
  have hhas : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    dsimp [F, F']
    have hg : HasDerivAt
        (fun x : ℝ => (x : ℂ) + (y : ℂ) * I - p) 1 x := by
      convert (hasDerivAt_ofReal x).add_const ((y : ℂ) * I - p) using 1
      ext z
      ring
    convert (hasDerivAt_const x (-C)).div hg (hne x) using 1
    ring
  have hd : deriv F = F' := funext fun x => (hhas x).deriv
  have hdiff : ∀ x ∈ Set.uIcc x₁ x₂, DifferentiableAt ℝ F x :=
    fun x _ => (hhas x).differentiableAt
  have hcont : Continuous F' := by
    dsimp [F']
    exact continuous_const.div
      (((continuous_ofReal.add continuous_const).sub continuous_const).pow 2)
      (fun x => pow_ne_zero 2 (hne x))
  simpa [HIntegral, F, F'] using
    intervalIntegral.integral_deriv_eq_sub' F hd hdiff hcont.continuousOn

private theorem vIntegral_const_div_sq (C p : ℂ) (x y₁ y₂ : ℝ)
    (hx : x ≠ p.re) :
    VIntegral (fun s : ℂ => C / (s - p) ^ 2) x y₁ y₂ =
      -C / ((x : ℂ) + (y₂ : ℂ) * I - p) -
        (-C / ((x : ℂ) + (y₁ : ℂ) * I - p)) := by
  let F : ℝ → ℂ := fun y => -C / ((x : ℂ) + (y : ℂ) * I - p)
  let F' : ℝ → ℂ := fun y => C * I / ((x : ℂ) + (y : ℂ) * I - p) ^ 2
  have hne : ∀ y : ℝ, ((x : ℂ) + (y : ℂ) * I - p) ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, mul_zero,
      ofReal_im, zero_mul, sub_zero, zero_re, add_zero] at hr
    exact hx (sub_eq_zero.mp hr)
  have hhas : ∀ y : ℝ, HasDerivAt F (F' y) y := by
    intro y
    dsimp [F, F']
    have hg : HasDerivAt
        (fun y : ℝ => (x : ℂ) + (y : ℂ) * I - p) I y := by
      convert ((hasDerivAt_ofReal y).mul_const I).add_const
        ((x : ℂ) - p) using 1
      · ext z
        ring
      · simp
    convert (hasDerivAt_const y (-C)).div hg (hne y) using 1
    ring
  have hd : deriv F = F' := funext fun y => (hhas y).deriv
  have hdiff : ∀ y ∈ Set.uIcc y₁ y₂, DifferentiableAt ℝ F y :=
    fun y _ => (hhas y).differentiableAt
  have hcont : Continuous F' := by
    dsimp [F']
    exact continuous_const.div
      (((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
        continuous_const).pow 2)
      (fun y => pow_ne_zero 2 (hne y))
  have hFTC := intervalIntegral.integral_deriv_eq_sub' F hd hdiff hcont.continuousOn
  rw [show F' = fun y : ℝ =>
      I * (C / ((x : ℂ) + (y : ℂ) * I - p) ^ 2) by
    funext y
    dsimp [F']
    ring] at hFTC
  rw [intervalIntegral.integral_const_mul] at hFTC
  simpa [VIntegral, F, smul_eq_mul] using hFTC

/-- The double-pole term has zero integral around every rectangle whose
interior contains the pole.  This is the exact higher-pole cancellation
needed before applying the repository's simple-pole residue theorem. -/
theorem rectangleIntegral'_const_div_sq_eq_zero {C p z w : ℂ}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s : ℂ => C / (s - p) ^ 2) z w = 0 := by
  have hp' := hp
  rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzre, Set.uIoo_of_le hzim,
    mem_reProdIm, Set.mem_Ioo] at hp'
  rcases hp' with ⟨⟨hzpRe, hpwRe⟩, ⟨hzpIm, hpwIm⟩⟩
  have hbottom := hIntegral_const_div_sq C p z.re w.re z.im
    (ne_of_lt hzpIm)
  have htop := hIntegral_const_div_sq C p z.re w.re w.im
    (ne_of_gt hpwIm)
  have hright := vIntegral_const_div_sq C p w.re z.im w.im
    (ne_of_gt hpwRe)
  have hleft := vIntegral_const_div_sq C p z.re z.im w.im
    (ne_of_lt hzpRe)
  unfold RectangleIntegral' RectangleIntegral
  rw [hbottom, htop, hright, hleft]
  ring

/-- Exact normalized rectangle integral of a holomorphic numerator divided
by a squared Cauchy kernel. -/
theorem rectangleIntegral'_div_sq_eq_deriv
    {N : ℂ → ℂ} {z w p : ℂ}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p)
    (hN : DifferentiableOn ℂ N (Rectangle z w)) :
    RectangleIntegral' (fun u : ℂ => N u / (u - p) ^ 2) z w =
      deriv N p := by
  let D : ℂ → ℂ := dslope N p
  let R : ℂ → ℂ := dslope D p
  let C : ℂ := N p
  let A : ℂ := D p
  let f : ℂ → ℂ := fun u => N u / (u - p) ^ 2
  let f₁ : ℂ → ℂ := fun u => f u - C / (u - p) ^ 2
  have hD : HolomorphicOn D (Rectangle z w) := by
    change DifferentiableOn ℂ D (Rectangle z w)
    dsimp only [D]
    exact (Complex.differentiableOn_dslope hp).2 hN
  have hR : HolomorphicOn R (Rectangle z w) := by
    change DifferentiableOn ℂ R (Rectangle z w)
    dsimp only [R]
    exact (Complex.differentiableOn_dslope hp).2 hD
  have hPrincipal : Set.EqOn
      (f₁ - fun u => A / (u - p)) R (Rectangle z w \ {p}) := by
    intro u hu
    have hup : u ≠ p := hu.2
    have hND := sub_smul_dslope N p u
    have hDR := sub_smul_dslope D p u
    change (u - p) * D u = N u - N p at hND
    change (u - p) * R u = D u - D p at hDR
    change N u / (u - p) ^ 2 - N p / (u - p) ^ 2 -
        D p / (u - p) = R u
    have huSub : u - p ≠ 0 := sub_ne_zero.mpr hup
    calc
      N u / (u - p) ^ 2 - N p / (u - p) ^ 2 - D p / (u - p) =
          (N u - N p) / (u - p) ^ 2 - D p / (u - p) := by ring
      _ = ((u - p) * D u) / (u - p) ^ 2 - D p / (u - p) := by
        rw [hND]
      _ = D u / (u - p) - D p / (u - p) := by
        field_simp [huSub]
      _ = (D u - D p) / (u - p) := by ring
      _ = ((u - p) * R u) / (u - p) := by rw [hDR]
      _ = R u := by field_simp [huSub]
  have hSimple := ResidueTheoremOnRectangleWithSimplePole
    (f := f₁) (g := R) (p := p) (A := A)
    hzre hzim hp hR hPrincipal
  have hDouble := rectangleIntegral'_const_div_sq_eq_zero
    (C := C) (p := p) hzre hzim hp
  have hf₁Holo : HolomorphicOn f₁ (Rectangle z w \ {p}) := by
    intro u hu
    have hup : u ≠ p := hu.2
    have huRect : u ∈ Rectangle z w := hu.1
    have hQuotient : DifferentiableWithinAt ℂ
        (fun v => N v / (v - p) ^ 2 - C / (v - p) ^ 2)
        (Rectangle z w) u := ((hN u huRect).div
        ((differentiableAt_id.sub_const p).pow 2).differentiableWithinAt
          (pow_ne_zero 2 (sub_ne_zero.mpr hup))).sub
      (differentiableWithinAt_const C |>.div
        ((differentiableAt_id.sub_const p).pow 2).differentiableWithinAt
          (pow_ne_zero 2 (sub_ne_zero.mpr hup)))
    simpa only [f₁, f] using hQuotient.mono (sdiff_subset)
  have hDoubleHolo : HolomorphicOn
      (fun u : ℂ => C / (u - p) ^ 2) (Rectangle z w \ {p}) := by
    intro u hu
    apply DifferentiableAt.differentiableWithinAt
    exact differentiableAt_const C |>.div
      ((differentiableAt_id.sub_const p).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr hu.2))
  have hf₁Int : RectangleBorderIntegrable f₁ z w :=
    HolomorphicOn.rectangleBorderIntegrable' hf₁Holo hp
  have hDoubleInt : RectangleBorderIntegrable
      (fun u : ℂ => C / (u - p) ^ 2) z w :=
    HolomorphicOn.rectangleBorderIntegrable' hDoubleHolo hp
  have hPoint : f = f₁ + fun u : ℂ => C / (u - p) ^ 2 := by
    funext u
    change f u = (f u - C / (u - p) ^ 2) + C / (u - p) ^ 2
    ring
  have hRectAdd : RectangleIntegral f z w = RectangleIntegral f₁ z w +
      RectangleIntegral (fun u : ℂ => C / (u - p) ^ 2) z w := by
    rw [hPoint]
    exact RectangleBorderIntegrable.add hf₁Int hDoubleInt
  have hA : A = deriv N p := by
    dsimp only [A, D]
    rw [dslope_same]
  change RectangleIntegral' f z w = deriv N p
  unfold RectangleIntegral' at hSimple hDouble ⊢
  rw [hRectAdd, smul_add, hSimple, hDouble, add_zero, hA]

end MathCollab.Density.Stronger.PointMean
