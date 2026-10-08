module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Source slices and exact hashes:
../../../../../third_party/twelfth/SQUARE_PORT_MANIFEST.json.
See ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local rectangle theorem preserves its PNT+ Apache-2.0 attribution.
-/
public import MathCollab.Density.RectangleResidue
public import MathCollab.Density.Stronger.Fourth.Coefficients
public import MathCollab.Density.Stronger.CriticalMoment
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology ArithmeticFunction
open MathCollab.Density.Contour MathCollab.Density.Stronger
open MathCollab.Density.Stronger.Fourth
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma BigOperators Interval
  LSeries.notation ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem arithmeticZeta_mul_self_eq_sigma_zero :
    (ζ : ArithmeticFunction ℕ) * ζ = ArithmeticFunction.sigma 0 := by
  ext n
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.zeta_apply,
    ArithmeticFunction.sigma_apply, mul_ite,
    mul_zero, mul_one, pow_zero, Finset.sum_const, smul_eq_mul]
  have key : ∀ x ∈ n.divisorsAntidiagonal,
      (if x.2 = 0 then 0 else if x.1 = 0 then 0 else 1) = 1 := by
    intro ⟨a, b⟩ hx
    have h := Nat.mem_divisorsAntidiagonal.mp hx
    simp [mul_ne_zero_iff.mp (h.1 ▸ h.2)]
  simp_rw [Finset.sum_congr rfl key, Finset.card_eq_sum_ones, Finset.sum_const]
  simp only [smul_eq_mul, mul_one, ← Nat.map_div_right_divisors]
  exact Finset.card_map
    { toFun := fun d => (d, n / d), inj' := fun x y h => congrArg Prod.fst h }

/-- The exact divisor-series expansion needed when the right AFE contour is
opened.  It is proved locally so the result does not import unrelated admitted
declarations from the newer PNT+ development. -/
theorem riemannZeta_sq_eq_divisorLSeries {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 2 =
      LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s := by
  have hNat : LSeries (↗((ζ : ArithmeticFunction ℕ) * ζ)) s =
      LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := by
    congr 1
    ext n
    simp only [← ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_apply]
  have hMul : LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s =
      LSeries (↗ζ) s * LSeries (↗ζ) s :=
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
  calc
    riemannZeta s ^ 2 = LSeries (↗ζ) s * LSeries (↗ζ) s := by
      rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, pow_two]
    _ = LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := hMul.symm
    _ = LSeries (↗((ζ : ArithmeticFunction ℕ) * ζ)) s := hNat.symm
    _ = LSeries (↗(ArithmeticFunction.sigma 0)) s := by
      rw [arithmeticZeta_mul_self_eq_sigma_zero]
    _ = LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s := by
      apply congrArg (fun f : ℕ → ℂ => LSeries f s)
      funext n
      simp [ArithmeticFunction.sigma_zero_apply]

/-- Absolute summability of the divisor Dirichlet series on the same right
half-plane on which `riemannZeta_sq_eq_divisorLSeries` opens the zeta square.
This is the convergence datum needed for the Hughes--Young Fubini steps; the
value identity alone is not enough to justify rearranging the two series. -/
theorem divisorLSeries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (n.divisors.card : ℂ)) s := by
  have hz : LSeriesSummable (⇑(ζ : ArithmeticFunction ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hconv : LSeriesSummable (⇑((ζ : ArithmeticFunction ℂ) * ζ)) s :=
    ArithmeticFunction.LSeriesSummable_mul hz hz
  apply (LSeriesSummable_congr s (f := ⇑((ζ : ArithmeticFunction ℂ) * ζ))
    (g := fun n : ℕ => (n.divisors.card : ℂ)) ?_).mp hconv
  intro n hn
  rw [← ArithmeticFunction.natCoe_mul]
  change (((((ζ : ArithmeticFunction ℕ) * ζ) n : ℕ) : ℂ)) = _
  rw [arithmeticZeta_mul_self_eq_sigma_zero]
  simp [ArithmeticFunction.sigma_zero_apply]



noncomputable def completedXiNumerator (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1



theorem completedXiNumerator_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedXiNumerator s = s * (1 - s) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  unfold completedXiNumerator
  have h1m : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1m]
  ring

theorem completedXiNumerator_one_sub (s : ℂ) :
    completedXiNumerator (1 - s) = completedXiNumerator s := by
  unfold completedXiNumerator
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem differentiable_completedXiNumerator :
    Differentiable ℂ completedXiNumerator := by
  unfold completedXiNumerator
  have hpoly : Differentiable ℂ (fun s : ℂ => s * (1 - s)) := by fun_prop
  exact (hpoly.mul differentiable_completedZeta₀).sub
    (differentiable_const (c := (1 : ℂ)))



@[simp] theorem one_sub_afeCriticalPoint (t : ℝ) :
    1 - afeCriticalPoint t = afeCriticalPoint (-t) := by
  unfold afeCriticalPoint
  push_cast
  ring

theorem afeCriticalPoint_ne_zero (t : ℝ) : afeCriticalPoint t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [afeCriticalPoint] at this

theorem afeCriticalPoint_ne_one (t : ℝ) : afeCriticalPoint t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [afeCriticalPoint] at this



noncomputable def hughesYoungAuxiliaryZero (w : ℂ) : ℂ :=
  (1 - 4 * w ^ 2) ^ 4

@[simp]
theorem hughesYoungAuxiliaryZero_zero :
    hughesYoungAuxiliaryZero 0 = 1 := by
  norm_num [hughesYoungAuxiliaryZero]

theorem hughesYoungAuxiliaryZero_neg (w : ℂ) :
    hughesYoungAuxiliaryZero (-w) = hughesYoungAuxiliaryZero w := by
  simp [hughesYoungAuxiliaryZero]

theorem differentiable_hughesYoungAuxiliaryZero :
    Differentiable ℂ hughesYoungAuxiliaryZero := by
  unfold hughesYoungAuxiliaryZero
  fun_prop



theorem completedRiemannZeta_eq_zeta_mul_GammaR {s : ℂ}
    (hs : 0 < s.re) :
    completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]



theorem afeCriticalPoint_neg_eq_star (t : ℝ) :
    afeCriticalPoint (-t) = star (afeCriticalPoint t) := by
  simp [afeCriticalPoint]

/-- Zeta at the lower critical point is the conjugate of zeta at the upper
critical point. -/
theorem riemannZeta_afeCriticalPoint_neg_eq_star (t : ℝ) :
    riemannZeta (afeCriticalPoint (-t)) =
      star (riemannZeta (afeCriticalPoint t)) := by
  rw [afeCriticalPoint_neg_eq_star]
  exact riemannZeta_conj _



/-- Pole normalization for one squared completed zeta factor. -/
noncomputable def zetaSquarePoleNormalization (t : ℝ) : ℂ :=
  (afeCriticalPoint t * (1 - afeCriticalPoint t)) ^ 2

theorem zetaSquarePoleNormalization_ne_zero (t : ℝ) :
    zetaSquarePoleNormalization t ≠ 0 := by
  unfold zetaSquarePoleNormalization
  exact pow_ne_zero 2 (mul_ne_zero (afeCriticalPoint_ne_zero t)
    (sub_ne_zero.mpr (afeCriticalPoint_ne_one t).symm))

theorem zetaSquarePoleNormalization_neg (t : ℝ) :
    zetaSquarePoleNormalization (-t) =
      zetaSquarePoleNormalization t := by
  unfold zetaSquarePoleNormalization
  rw [show afeCriticalPoint (-t) = 1 - afeCriticalPoint t by
    symm
    exact one_sub_afeCriticalPoint t]
  ring

theorem zetaSquarePoleNormalization_eq (t : ℝ) :
    zetaSquarePoleNormalization t = (((1 / 4 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  unfold zetaSquarePoleNormalization afeCriticalPoint
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem zetaSquarePoleNormalization_norm_lower (t : ℝ) :
    1 / 16 ≤ ‖zetaSquarePoleNormalization t‖ := by
  rw [zetaSquarePoleNormalization_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

/-- Entire numerator for the one-sided squared-zeta AFE. -/
noncomputable def zetaSquareContourNumerator
    (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    completedXiNumerator (afeCriticalPoint t + w) ^ 2 /
      zetaSquarePoleNormalization t

theorem differentiable_zetaSquareContourNumerator (t : ℝ) :
    Differentiable ℂ (zetaSquareContourNumerator t) := by
  unfold zetaSquareContourNumerator
  have hshift : Differentiable ℂ (fun w : ℂ => afeCriticalPoint t + w) := by
    fun_prop
  have hxi : Differentiable ℂ
      (fun w : ℂ => completedXiNumerator (afeCriticalPoint t + w)) :=
    fun w => differentiable_completedXiNumerator.differentiableAt.comp w
      (hshift w)
  have haux : Differentiable ℂ hughesYoungAuxiliaryZero :=
    differentiable_hughesYoungAuxiliaryZero
  fun_prop (disch := assumption)

/-- Functional-equation reflection of the one-sided numerator. -/
theorem zetaSquareContourNumerator_neg (t : ℝ) (w : ℂ) :
    zetaSquareContourNumerator t (-w) =
      zetaSquareContourNumerator (-t) w := by
  unfold zetaSquareContourNumerator
  rw [show afeCriticalPoint t + -w =
      1 - (afeCriticalPoint (-t) + w) by
        unfold afeCriticalPoint
        push_cast
        ring,
    completedXiNumerator_one_sub, hughesYoungAuxiliaryZero_neg,
    zetaSquarePoleNormalization_neg]
  simp only [neg_sq]

/-- The residue is the literal square of the completed zeta value. -/
theorem zetaSquareContourNumerator_zero (t : ℝ) :
    zetaSquareContourNumerator t 0 =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 := by
  simp only [zetaSquareContourNumerator,
    zero_pow (by decide : 2 ≠ 0), mul_zero, exp_zero,
    hughesYoungAuxiliaryZero_zero, one_mul, add_zero]
  rw [completedXiNumerator_eq _
      (afeCriticalPoint_ne_zero t) (afeCriticalPoint_ne_one t)]
  rw [div_eq_iff (zetaSquarePoleNormalization_ne_zero t)]
  unfold zetaSquarePoleNormalization
  ring

noncomputable def zetaSquareContourIntegrand
    (t : ℝ) (w : ℂ) : ℂ :=
  zetaSquareContourNumerator t w / w

/-- Reflection changes the sign of the Cauchy kernel and the height. -/
theorem zetaSquareContourIntegrand_neg (t : ℝ) (w : ℂ) :
    zetaSquareContourIntegrand t (-w) =
      -zetaSquareContourIntegrand (-t) w := by
  unfold zetaSquareContourIntegrand
  rw [zetaSquareContourNumerator_neg]
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

/-- Exact residue theorem for the one-sided square. -/
theorem zetaSquare_finiteRectangle
    (t : ℝ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    RectangleIntegral'
        (fun w : ℂ => zetaSquareContourNumerator t w / w)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 := by
  let F : ℂ → ℂ := zetaSquareContourNumerator t
  let z : ℂ := (-c : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  have hF : Differentiable ℂ F :=
    differentiable_zetaSquareContourNumerator t
  have hzero : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      uIoo_of_le (by simp [z, w]; linarith : z.re ≤ w.re),
      uIoo_of_le (by simp [z, w]; linarith : z.im ≤ w.im)]
    simp [z, w, hc, hH]
  have hdslope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    rw [differentiableOn_dslope
      (show Rectangle z w ∈ 𝓝 (0 : ℂ) from hzero)]
    exact hF.differentiableOn
  have hprincipal : Set.EqOn
      ((fun u : ℂ => F u / u) - fun u => F 0 / (u - 0))
      (dslope F 0) (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    rw [Pi.sub_apply, dslope_of_ne F hu0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp
  have hrect := ResidueTheoremOnRectangleWithSimplePole
    (f := fun u : ℂ => F u / u) (g := dslope F 0)
    (p := 0) (A := F 0)
    (zRe_le_wRe := by simp [z, w]; linarith)
    (zIm_le_wIm := by simp [z, w]; linarith)
    hzero hdslope hprincipal
  simpa [F, z, w, zetaSquareContourNumerator_zero] using hrect


theorem hIntegral_zetaSquare_bottom (t c H : ℝ) :
    HIntegral (zetaSquareContourIntegrand t) (-c) c (-H) =
      -HIntegral (zetaSquareContourIntegrand (-t)) (-c) c H := by
  let f := zetaSquareContourIntegrand t
  let g := zetaSquareContourIntegrand (-t)
  have hpoint : ∀ x : ℝ,
      f ((x : ℂ) + (-H : ℂ) * I) =
        -g (((-x : ℝ) : ℂ) + (H : ℂ) * I) := by
    intro x
    have harg : (x : ℂ) + (-H : ℂ) * I =
        -(((-x : ℝ) : ℂ) + (H : ℂ) * I) := by push_cast; ring
    rw [harg]
    exact zetaSquareContourIntegrand_neg t _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => g ((x : ℂ) + (H : ℂ) * I))
    (a := -c) (b := c)
  simp only [neg_neg] at hcomp
  change (∫ x in -c..c, f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) =
    -(∫ x in -c..c, g ((x : ℂ) + (H : ℂ) * I))
  calc
    _ = -∫ x in -c..c, g (((-x : ℝ) : ℂ) + (H : ℂ) * I) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _hx
      simpa only [ofReal_neg] using hpoint x
    _ = _ := by
      rw [hcomp]

theorem vIntegral_zetaSquare_left (t c H : ℝ) :
    VIntegral (zetaSquareContourIntegrand t) (-c) (-H) H =
      -VIntegral (zetaSquareContourIntegrand (-t)) c (-H) H := by
  let f := zetaSquareContourIntegrand t
  let g := zetaSquareContourIntegrand (-t)
  have hpoint : ∀ y : ℝ,
      f (((-c : ℝ) : ℂ) + (y : ℂ) * I) =
        -g ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    intro y
    have harg : (((-c : ℝ) : ℂ) + (y : ℂ) * I) =
        -((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [harg]
    exact zetaSquareContourIntegrand_neg t _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ => g ((c : ℂ) + (y : ℂ) * I))
    (a := -H) (b := H)
  simp only [neg_neg] at hcomp
  have hraw :
    (∫ y in -H..H, f (((-c : ℝ) : ℂ) + (y : ℂ) * I)) =
        -∫ y in -H..H, g ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _hy
      simpa only [ofReal_neg] using hpoint y
  have hraw' :
      (∫ y in -H..H, f (((-c : ℝ) : ℂ) + (y : ℂ) * I)) =
        -(∫ y in -H..H, g ((c : ℂ) + (y : ℂ) * I)) := by
    calc
      _ = -∫ y in -H..H, g ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := hraw
      _ = _ := by rw [hcomp]
  unfold VIntegral
  rw [hraw']
  simp [g]

/-- Finite-height one-sided AFE with both reflected right contours and both
horizontal errors displayed. -/
theorem zetaSquareAFE_truncated_native
    (t : ℝ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 =
      VIntegral' (zetaSquareContourIntegrand t) c (-H) H +
      VIntegral' (zetaSquareContourIntegrand (-t)) c (-H) H -
      HIntegral' (zetaSquareContourIntegrand t) (-c) c H -
      HIntegral' (zetaSquareContourIntegrand (-t)) (-c) c H := by
  have hrect := zetaSquare_finiteRectangle t hc hH
  change RectangleIntegral'
      (zetaSquareContourIntegrand t)
      ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) = _ at hrect
  rw [show RectangleIntegral'
        (zetaSquareContourIntegrand t)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      VIntegral' (zetaSquareContourIntegrand t) c (-H) H +
      VIntegral' (zetaSquareContourIntegrand (-t)) c (-H) H -
      HIntegral' (zetaSquareContourIntegrand t) (-c) c H -
      HIntegral' (zetaSquareContourIntegrand (-t)) (-c) c H by
    unfold RectangleIntegral' RectangleIntegral HIntegral' VIntegral'
    simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
    rw [hIntegral_zetaSquare_bottom,
      vIntegral_zetaSquare_left]
    ring] at hrect
  exact hrect.symm



def zetaSquareGammaNormalization (t : ℝ) : ℂ :=
  Gammaℝ (afeCriticalPoint t) * Gammaℝ (afeCriticalPoint (-t))

theorem zetaSquareGammaNormalization_ne_zero (t : ℝ) :
    zetaSquareGammaNormalization t ≠ 0 := by
  exact mul_ne_zero
    (Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint]))
    (Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint]))

theorem zetaSquareGammaNormalization_neg (t : ℝ) :
    zetaSquareGammaNormalization (-t) = zetaSquareGammaNormalization t := by
  simp [zetaSquareGammaNormalization, mul_comm]

theorem completedZeta_square_eq_norm_mul_gamma (t : ℝ) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 =
      (zetaMomentCriticalNorm t ^ 2 : ℝ) * zetaSquareGammaNormalization t := by
  have hreflection : completedRiemannZeta (afeCriticalPoint (-t)) =
      completedRiemannZeta (afeCriticalPoint t) := by
    rw [← one_sub_afeCriticalPoint, completedRiemannZeta_one_sub]
  have hnorm : ((zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) =
      riemannZeta (afeCriticalPoint t) * riemannZeta (afeCriticalPoint (-t)) := by
    rw [riemannZeta_afeCriticalPoint_neg_eq_star]
    simp only [zetaMomentCriticalNorm, afeCriticalPoint, Complex.ofReal_div, Complex.ofReal_one]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    exact mul_comm _ _
  calc
    _ = completedRiemannZeta (afeCriticalPoint t) *
        completedRiemannZeta (afeCriticalPoint (-t)) := by rw [hreflection, pow_two]
    _ = (riemannZeta (afeCriticalPoint t) * Gammaℝ (afeCriticalPoint t)) *
        (riemannZeta (afeCriticalPoint (-t)) * Gammaℝ (afeCriticalPoint (-t))) := by
      rw [completedRiemannZeta_eq_zeta_mul_GammaR (by norm_num [afeCriticalPoint]),
        completedRiemannZeta_eq_zeta_mul_GammaR (by norm_num [afeCriticalPoint])]
    _ = _ := by rw [hnorm]; unfold zetaSquareGammaNormalization; ring



/-- The actual critical-line zeta norm is exactly the normalized finite contour,
with both horizontal errors retained. -/
theorem zetaSquareNorm_eq_truncated_source
    (t : ℝ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    zetaMomentCriticalNorm t ^ 2 =
      ((VIntegral' (zetaSquareContourIntegrand t) c (-H) H +
        VIntegral' (zetaSquareContourIntegrand (-t)) c (-H) H -
        HIntegral' (zetaSquareContourIntegrand t) (-c) c H -
        HIntegral' (zetaSquareContourIntegrand (-t)) (-c) c H) /
          zetaSquareGammaNormalization t).re := by
  rw [← zetaSquareAFE_truncated_native t hc hH,
    completedZeta_square_eq_norm_mul_gamma,
    mul_div_cancel_right₀ _ (zetaSquareGammaNormalization_ne_zero t), Complex.ofReal_re]

end MathCollab.Density.Stronger.Fourth
