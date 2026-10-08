module
-- Reversible module-visibility port of the audited development.
/-
Native modulus-one specialization using Mathlib's actual zeta functional equation
and the exact McColm Voronoi multiplier conventions (MIT-0, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1).
See repository-root third_party/twelfth/LICENSE-MIT-0. Mathlib Apache attribution retained.
No general-modulus Estermann input or assumed Voronoi identity is used.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiTransforms

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem four_mul_cos_half_sq (w : ℂ) :
    4 * Complex.cos (w / 2) ^ 2 =
      Complex.exp (w * I) + Complex.exp (-(w * I)) + 2 := by
  rw [Complex.cos_sq, show 2 * (w / 2) = w by ring]
  unfold Complex.cos
  ring

theorem riemannZeta_eq_voronoiFactor {z : ℂ} (hz : z.re < 1) (hz0 : z ≠ 0) :
    riemannZeta z = 2 * dfiPeriodicArchimedeanFactor 1 (1 - z) *
      Complex.cos (Real.pi * (1 - z) / 2) * riemannZeta (1 - z) := by
  have hr : 0 < (1 - z).re := by simp only [sub_re, one_re]; linarith
  have hn : ∀ n : ℕ, 1 - z ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne : 1 - z ≠ 1 := by
    intro h
    apply hz0
    linear_combination -h
  have h := riemannZeta_one_sub hn hne
  rw [show 1 - (1 - z) = z by ring] at h
  simpa [dfiPeriodicArchimedeanFactor, mul_assoc] using h

theorem riemannZeta_sq_eq_voronoiMultipliers {z : ℂ} (hz : z.re < 1) (hz0 : z ≠ 0) :
    riemannZeta z ^ 2 =
      (dfiVoronoiMinusMultiplier 1 z + dfiVoronoiPlusMultiplier 1 z) *
        riemannZeta (1 - z) ^ 2 := by
  have hc := four_mul_cos_half_sq (Real.pi * (1 - z))
  have hp : Complex.exp (Real.pi * (1 - z) * I) =
      Complex.exp (Real.pi * I * (1 - z)) := by congr 1; ring
  have hm : Complex.exp (-(Real.pi * (1 - z) * I)) =
      Complex.exp (-Real.pi * I * (1 - z)) := by congr 1; ring
  rw [hp, hm] at hc
  rw [riemannZeta_eq_voronoiFactor hz hz0]
  unfold dfiVoronoiMinusMultiplier dfiVoronoiPlusMultiplier
  simp only [Nat.cast_one, one_mul, mul_one]
  calc
    _ = dfiPeriodicArchimedeanFactor 1 (1 - z) ^ 2 *
        (4 * Complex.cos (Real.pi * (1 - z) / 2) ^ 2) * riemannZeta (1 - z) ^ 2 := by ring
    _ = _ := by rw [hc]; ring

end MathCollab.Density.Stronger.Atkinson
