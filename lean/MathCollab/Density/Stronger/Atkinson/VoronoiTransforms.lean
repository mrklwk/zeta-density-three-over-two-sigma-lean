module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIVoronoiDual.lean,
exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/BESSEL_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain
Apache-2.0 attribution. No Estermann or general-modulus source closure is imported.
-/
public import MathCollab.Density.Stronger.PointMean.MellinShift

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open scoped Topology Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

noncomputable def dfiPeriodicArchimedeanFactor (q : ℕ) [NeZero q]
    (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Gamma s

/-- The common Voronoi archimedean factor is holomorphic in the positive
half-plane.  This is the pole-free region traversed when the dual Mellin
contour is shifted to the left. -/
theorem differentiableAt_dfiPeriodicArchimedeanFactor_of_re_pos
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (dfiPeriodicArchimedeanFactor q) s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hGamma : DifferentiableAt ℂ Gamma s :=
    Complex.differentiableAt_Gamma s (fun m hm => by
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith)
  exact (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hq)).mul
    (differentiableAt_id.neg.const_cpow (Or.inl hpi))).mul hGamma

noncomputable def dfiVoronoiMinusMultiplier (q : ℕ) [NeZero q]
    (z : ℂ) : ℂ :=
  (q : ℂ) * dfiPeriodicArchimedeanFactor q (1 - z) ^ 2 *
    (cexp (Real.pi * I * (1 - z)) + cexp (-Real.pi * I * (1 - z)))

/-- Mellin multiplier of DFI's `K₀` (mixed-sign) Voronoi branch. -/
noncomputable def dfiVoronoiPlusMultiplier (q : ℕ) [NeZero q]
    (z : ℂ) : ℂ :=
  2 * (q : ℂ) * dfiPeriodicArchimedeanFactor q (1 - z) ^ 2

/-- Both DFI dual multipliers are holomorphic to the left of `Re z = 1`.
This is the analytic input for arbitrary repeated contour shifts in (29). -/
theorem differentiableAt_dfiVoronoiMinusMultiplier_of_re_lt_one
    (q : ℕ) [NeZero q] {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiVoronoiMinusMultiplier q) z := by
  have hinner : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hfactor := (differentiableAt_dfiPeriodicArchimedeanFactor_of_re_pos q
    (s := 1 - z) (by simpa using sub_pos.mpr hz)).comp z hinner
  unfold dfiVoronoiMinusMultiplier
  exact ((differentiableAt_const (c := (q : ℂ))).mul (hfactor.pow 2)).mul
    ((Complex.differentiableAt_exp.comp z (by fun_prop)).add
      (Complex.differentiableAt_exp.comp z (by fun_prop)))

theorem differentiableAt_dfiVoronoiPlusMultiplier_of_re_lt_one
    (q : ℕ) [NeZero q] {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiVoronoiPlusMultiplier q) z := by
  have hinner : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hfactor := (differentiableAt_dfiPeriodicArchimedeanFactor_of_re_pos q
    (s := 1 - z) (by simpa using sub_pos.mpr hz)).comp z hinner
  unfold dfiVoronoiPlusMultiplier
  exact ((differentiableAt_const (c := (2 : ℂ))).mul
    (differentiableAt_const (c := (q : ℂ)))).mul (hfactor.pow 2)

/-- DFI's negative-sign Bessel transform in its canonical Mellin--Barnes
form.  The source normalization is
`-(2π/q) ∫ g(x) Y₀(4π√(xy)/q) dx`; its Mellin multiplier is the
equal-sign branch above. -/
noncomputable def dfiVoronoiMinusTransform (q : ℕ) [NeZero q]
    (G : ℂ → ℂ) (n : ℕ) : ℂ :=
  PointMean.VerticalIntegral' (fun z : ℂ =>
    ((n : ℂ) ^ (-(1 - z))) * dfiVoronoiMinusMultiplier q z * G z)
    (-(1 / 2 : ℝ))

/-- DFI's positive-sign modified-Bessel transform in canonical
Mellin--Barnes form.  Its source normalization is
`(4/q) ∫ g(x) K₀(4π√(xy)/q) dx`. -/
noncomputable def dfiVoronoiPlusTransform (q : ℕ) [NeZero q]
    (G : ℂ → ℂ) (n : ℕ) : ℂ :=
  PointMean.VerticalIntegral' (fun z : ℂ =>
    ((n : ℂ) ^ (-(1 - z))) * dfiVoronoiPlusMultiplier q z * G z)
    (-(1 / 2 : ℝ))


/-- Exact real-parameter normalization of the existing vertical contour. -/
theorem verticalIntegral'_eq_realIntegral (f : ℂ → ℂ) (a : ℝ) :
    PointMean.VerticalIntegral' f a = (1 / (2 * Real.pi) : ℂ) *
      ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I) := by
  unfold PointMean.VerticalIntegral' PointMean.VerticalIntegral
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

end MathCollab.Density.Stronger.Atkinson
