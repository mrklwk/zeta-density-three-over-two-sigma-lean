module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIBesselTransformBridge.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselTransforms

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- The mixed-sign DFI multiplier is exactly the Mellin transform of the
scaled `K₀` kernel, including every factor of `2`, `π`, and `q`. -/
theorem dfiVoronoiPlusMultiplier_eq_scaled_K0_mellin
    (q n : ℕ) [NeZero q] (hn : 0 < n) (z : ℂ)
    (hz : 0 < (1 - z).re) :
    (n : ℂ) ^ (-(1 - z)) * dfiVoronoiPlusMultiplier q z =
      (4 / (q : ℂ)) * mellin
        (fun x : ℝ => (dfiBesselK0
          ((4 * Real.pi * Real.sqrt n / q) * Real.sqrt x) : ℂ))
        (1 - z) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let A : ℝ := 4 * Real.pi * Real.sqrt n / q
  have hA : 0 < A := by dsimp [A]; positivity
  rw [mellin_dfiBesselK0_mul_sqrt hA hz]
  dsimp [A]
  rw [dfiBesselK0MellinSymbol_two_mul]
  unfold dfiVoronoiPlusMultiplier dfiPeriodicArchimedeanFactor
  ring_nf
  have hsplit (e : ℂ) :
      ((Real.pi * Real.sqrt n * (q : ℝ)⁻¹ * 4 : ℝ) : ℂ) ^ e =
        (Real.pi : ℂ) ^ e * (Real.sqrt n : ℂ) ^ e *
          (((q : ℝ)⁻¹ : ℝ) : ℂ) ^ e * (4 : ℂ) ^ e := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      (mul_nonneg (mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (Nat.cast_nonneg q))) (by norm_num)]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      (mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (Nat.cast_nonneg q))]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      Real.pi_nonneg (Real.sqrt_nonneg _)]
    norm_num
  rw [hsplit]
  have hsqrtSq : ((Real.sqrt n : ℂ) ^ (2 : ℕ)) = (n : ℂ) := by
    rw [show (Real.sqrt n : ℂ) = ((Real.sqrt n : ℝ) : ℂ) by rfl,
      ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  have hsqrtArg : Complex.arg (Real.sqrt n : ℂ) = 0 := by
    exact Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg _)
  have hsqrtPow : (Real.sqrt n : ℂ) ^ (-2 + z * 2) =
      (n : ℂ) ^ (-1 + z) := by
    have hcp := Complex.cpow_nat_mul'
      (n := 2) (x := (Real.sqrt n : ℂ))
      (by simp [hsqrtArg, Real.pi_pos])
      (by simp [hsqrtArg, Real.pi_pos.le]) (-1 + z)
    calc
      (Real.sqrt n : ℂ) ^ (-2 + z * 2) =
          (Real.sqrt n : ℂ) ^ ((2 : ℕ) * (-1 + z)) := by
            congr 1
            norm_num
            ring
      _ = ((Real.sqrt n : ℂ) ^ (2 : ℕ)) ^ (-1 + z) := hcp
      _ = (n : ℂ) ^ (-1 + z) := by rw [hsqrtSq]
  rw [hsqrtPow]
  have hPiTwo (e : ℂ) : ((Real.pi : ℂ) * 2) ^ e =
      (Real.pi : ℂ) ^ e * (2 : ℂ) ^ e := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg
        (by norm_num : (0 : ℝ) ≤ 2) e
  have hPiTwoSq (e : ℂ) : (((Real.pi : ℂ) * 2) ^ e) ^ 2 =
      (Real.pi : ℂ) ^ (e + e) * (2 : ℂ) ^ (e + e) := by
    rw [hPiTwo, pow_two]
    rw [show ((Real.pi : ℂ) ^ e * 2 ^ e) *
        ((Real.pi : ℂ) ^ e * 2 ^ e) =
      ((Real.pi : ℂ) ^ e * (Real.pi : ℂ) ^ e) *
        ((2 : ℂ) ^ e * (2 : ℂ) ^ e) by ring]
    rw [← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [hPiTwoSq]
  have hFour (e : ℂ) : (4 : ℂ) ^ e =
      (2 : ℂ) ^ e * (2 : ℂ) ^ e := by
    convert Complex.mul_cpow_ofReal_nonneg
      (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2) e using 1
    · norm_num
  rw [hFour, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  have hqArg : Complex.arg (q : ℂ) = 0 := by simp
  have hqInvPow (e : ℂ) : (((q : ℝ)⁻¹ : ℝ) : ℂ) ^ e =
      ((q : ℂ) ^ e)⁻¹ := by
    rw [Complex.ofReal_inv]
    apply Complex.inv_cpow (q : ℂ) e
    rw [hqArg]
    exact Real.pi_ne_zero.symm
  rw [hqInvPow]
  ring_nf
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hqLeft : (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
      (q : ℂ) ^ (1 - 2 * z) := by
    have hsq : ((q : ℂ) ^ (-z)) ^ 2 =
        (q : ℂ) ^ (2 * (-z)) := by
      symm
      convert Complex.cpow_nat_mul (q : ℂ) 2 (-z) using 1
    calc
      (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
          (q : ℂ) ^ (1 : ℂ) * (q : ℂ) ^ (2 * (-z)) := by
            rw [Complex.cpow_one, hsq]
      _ = (q : ℂ) ^ ((1 : ℂ) + 2 * (-z)) := by
            rw [Complex.cpow_add _ _ hq0]
      _ = (q : ℂ) ^ (1 - 2 * z) := by congr 1; ring
  have hqRight : (q : ℂ)⁻¹ * ((q : ℂ) ^ (-2 + z * 2))⁻¹ =
      (q : ℂ) ^ (1 - 2 * z) := by
    rw [← Complex.cpow_neg_one]
    rw [← Complex.cpow_neg _ (-2 + z * 2)]
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    ring
  have h2Left : (2 : ℂ) ^ (-2 + z * 2) * 2 =
      (2 : ℂ) ^ (-1 + z * 2) := by
    calc
      (2 : ℂ) ^ (-2 + z * 2) * 2 =
          (2 : ℂ) ^ (-2 + z * 2) * (2 : ℂ) ^ (1 : ℂ) := by simp
      _ = (2 : ℂ) ^ ((-2 + z * 2) + 1) := by
        rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      _ = (2 : ℂ) ^ (-1 + z * 2) := by congr 1; ring
  have h2Right : (2 : ℂ) ^ (-4 + z * 4) *
        (2 : ℂ) ^ (-(z * 2)) * 8 =
      (2 : ℂ) ^ (-1 + z * 2) := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    rw [show (8 : ℂ) = (2 : ℂ) ^ (3 : ℂ) by norm_num]
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    ring
  calc
    (n : ℂ) ^ (-1 + z) * (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 *
          (Real.pi : ℂ) ^ (-2 + z * 2) * (2 : ℂ) ^ (-2 + z * 2) *
          Gamma (1 - z) ^ 2 * 2 =
        (n : ℂ) ^ (-1 + z) * (q : ℂ) ^ (1 - 2 * z) *
          (Real.pi : ℂ) ^ (-2 + z * 2) *
          (2 : ℂ) ^ (-1 + z * 2) * Gamma (1 - z) ^ 2 := by
            rw [show (n : ℂ) ^ (-1 + z) * (q : ℂ) *
                ((q : ℂ) ^ (-z)) ^ 2 * (Real.pi : ℂ) ^ (-2 + z * 2) *
                (2 : ℂ) ^ (-2 + z * 2) * Gamma (1 - z) ^ 2 * 2 =
              (n : ℂ) ^ (-1 + z) *
                ((q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2) *
                (Real.pi : ℂ) ^ (-2 + z * 2) *
                ((2 : ℂ) ^ (-2 + z * 2) * 2) * Gamma (1 - z) ^ 2 by ring]
            rw [hqLeft, h2Left]
    _ = (n : ℂ) ^ (-1 + z) *
          ((q : ℂ)⁻¹ * ((q : ℂ) ^ (-2 + z * 2))⁻¹) *
          (Real.pi : ℂ) ^ (-2 + z * 2) *
          ((2 : ℂ) ^ (-4 + z * 4) *
            (2 : ℂ) ^ (-(z * 2)) * 8) * Gamma (1 - z) ^ 2 := by
            rw [← hqRight, ← h2Right]
    _ = Gamma (1 - z) ^ 2 * (q : ℂ)⁻¹ *
          ((Real.pi : ℂ) ^ (-2 + z * 2) * (n : ℂ) ^ (-1 + z) *
            ((q : ℂ) ^ (-2 + z * 2))⁻¹ * (2 : ℂ) ^ (-4 + z * 4)) *
          (2 : ℂ) ^ (-(z * 2)) * 8 := by
            simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = (n : ℂ) ^ (-1 + z) * (Real.pi : ℂ) ^ (-2 + z * 2) *
          Gamma (1 - z) ^ 2 * (q : ℂ)⁻¹ *
          ((q : ℂ) ^ (-2 + z * 2))⁻¹ *
          (2 : ℂ) ^ (-4 + z * 4) * (2 : ℂ) ^ (-(z * 2)) * 8 := by
            simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Two vertical integrals agree when their integrands agree on the line of
integration. -/
theorem verticalIntegral'_congr_line {f h : ℂ → ℂ} (σ : ℝ)
    (heq : ∀ u : ℝ,
      f ((σ : ℂ) + (u : ℂ) * I) = h ((σ : ℂ) + (u : ℂ) * I)) :
    PointMean.VerticalIntegral' f σ = PointMean.VerticalIntegral' h σ := by
  unfold PointMean.VerticalIntegral' PointMean.VerticalIntegral
  rw [show (∫ t : ℝ, f ((σ : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, h ((σ : ℂ) + (t : ℂ) * I) by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [heq u]]

/-- Constant factors may be pulled through a complete vertical integral. -/
theorem verticalIntegral'_const_mul_bridge (c : ℂ) (f : ℂ → ℂ) (σ : ℝ) :
    PointMean.VerticalIntegral' (fun z : ℂ => c * f z) σ =
      c * PointMean.VerticalIntegral' f σ := by
  unfold PointMean.VerticalIntegral' PointMean.VerticalIntegral
  simp only [smul_eq_mul]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The Mellin--Barnes mixed-sign transform occurring after DFI equation
(23) is the literal `K₀` transform in equation (29). -/
theorem dfiVoronoiPlusTransform_mellin_eq_bessel
    (q n : ℕ) [NeZero q] (hn : 0 < n) {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) :
    dfiVoronoiPlusTransform q (mellin g) n =
      dfiVoronoiPlusBesselTransform q g n := by
  let A : ℝ := 4 * Real.pi * Real.sqrt n / q
  let h : ℝ → ℂ := fun x => (dfiBesselK0 (A * Real.sqrt x) : ℂ)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : 0 < A := by dsimp [A]; positivity
  have hConv : MellinConvergent h (3 / 2 : ℂ) := by
    simpa only [h] using
      (mellinConvergent_dfiBesselK0_mul_sqrt hA
        (s := (3 / 2 : ℂ)) (by norm_num))
  have hMeas : AEStronglyMeasurable h
      (volume.restrict (Set.Ioi 0)) :=
    MellinConvergent.aestronglyMeasurable_positive hConv
  have hInt : IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) * ‖h x‖)
      (Set.Ioi 0) := by
    simpa only [show (3 / 2 : ℂ).re - 1 = (1 / 2 : ℝ) by norm_num] using
      MellinConvergent.integrableOn_rpow_mul_norm hConv
  have hPair := verticalIntegral'_mellin_mul_mellin_one_sub hg
    (-(1 / 2 : ℝ)) hMeas (by
      simpa only [neg_neg] using hInt)
  have hLine (u : ℝ) :
      (n : ℂ) ^ (-(1 - ((↑(-(1 / 2 : ℝ)) : ℂ) + (u : ℂ) * I))) *
            dfiVoronoiPlusMultiplier q
              ((↑(-(1 / 2 : ℝ)) : ℂ) + (u : ℂ) * I) *
            mellin g ((↑(-(1 / 2 : ℝ)) : ℂ) + (u : ℂ) * I) =
        (4 / (q : ℂ)) *
          (mellin g ((↑(-(1 / 2 : ℝ)) : ℂ) + (u : ℂ) * I) *
            mellin h
              (1 - ((↑(-(1 / 2 : ℝ)) : ℂ) + (u : ℂ) * I))) := by
    rw [dfiVoronoiPlusMultiplier_eq_scaled_K0_mellin q n hn]
    · dsimp [h, A]
      ring
    · norm_num
  have hKernel (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
      h x = (dfiBesselK0
        (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ) := by
    dsimp [h, A]
    congr 2
    rw [Real.sqrt_mul hx.le]
    ring
  unfold dfiVoronoiPlusTransform
  calc
    PointMean.VerticalIntegral' (fun z : ℂ =>
        (n : ℂ) ^ (-(1 - z)) * dfiVoronoiPlusMultiplier q z * mellin g z)
        (-(1 / 2 : ℝ)) =
      PointMean.VerticalIntegral' (fun z : ℂ =>
        (4 / (q : ℂ)) * (mellin g z * mellin h (1 - z)))
        (-(1 / 2 : ℝ)) :=
      verticalIntegral'_congr_line (-(1 / 2 : ℝ)) hLine
    _ = (4 / (q : ℂ)) * PointMean.VerticalIntegral' (fun z : ℂ =>
        mellin g z * mellin h (1 - z)) (-(1 / 2 : ℝ)) := by
      rw [verticalIntegral'_const_mul_bridge]
    _ = (4 / (q : ℂ)) * ∫ x : ℝ in Set.Ioi 0, g x * h x := by
      rw [hPair]
    _ = dfiVoronoiPlusBesselTransform q g n := by
      unfold dfiVoronoiPlusBesselTransform
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change g x * h x =
        g x * (dfiBesselK0
          (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)
      rw [hKernel x hx]

/-- The analytically continued Mellin symbol of `Y₀` differs from the
`K₀` symbol by the classical cosine factor. -/
theorem dfiBesselY0MellinSymbol_eq_cos_mul_K0 (w : ℂ) :
    dfiBesselY0MellinSymbol (2 * w) =
      -(2 / Real.pi : ℂ) * Complex.cos (Real.pi * w) *
        dfiBesselK0MellinSymbol (2 * w) := by
  rw [dfiBesselY0MellinSymbol_two_mul,
    dfiBesselK0MellinSymbol_two_mul]
  have h2 : (2 : ℂ) ^ (2 * w - 1) =
      2 * (2 : ℂ) ^ (2 * w - 2) := by
    calc
      (2 : ℂ) ^ (2 * w - 1) =
          (2 : ℂ) ^ ((1 : ℂ) + (2 * w - 2)) := by congr 1; ring
      _ = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (2 * w - 2) := by
        rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      _ = 2 * (2 : ℂ) ^ (2 * w - 2) := by simp
  rw [h2]
  ring

/-- Exact analytic-continuation identity for the equal-sign DFI
multiplier.  The right side is the scaled `Y₀` Mellin symbol before the
regularized Mellin inversion is applied. -/
theorem dfiVoronoiMinusMultiplier_eq_scaled_Y0_symbol
    (q n : ℕ) [NeZero q] (hn : 0 < n) (z : ℂ)
    (hz : 0 < (1 - z).re) :
    (n : ℂ) ^ (-(1 - z)) * dfiVoronoiMinusMultiplier q z =
      (-(2 * Real.pi) / (q : ℂ)) *
        (2 * ((4 * Real.pi * Real.sqrt n / q : ℝ) : ℂ) ^
          (-(2 * (1 - z))) * dfiBesselY0MellinSymbol (2 * (1 - z))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPlus := dfiVoronoiPlusMultiplier_eq_scaled_K0_mellin q n hn z hz
  rw [mellin_dfiBesselK0_mul_sqrt
    (by positivity : 0 < 4 * Real.pi * Real.sqrt n / q) hz] at hPlus
  have hRatio := dfiBesselY0MellinSymbol_eq_cos_mul_K0 (1 - z)
  have hCos :
      cexp (Real.pi * I * (1 - z)) + cexp (-Real.pi * I * (1 - z)) =
        2 * Complex.cos (Real.pi * (1 - z)) := by
    unfold Complex.cos
    ring_nf
  have hLeft :
      (n : ℂ) ^ (-(1 - z)) * dfiVoronoiMinusMultiplier q z =
        ((n : ℂ) ^ (-(1 - z)) * dfiVoronoiPlusMultiplier q z) *
          Complex.cos (Real.pi * (1 - z)) := by
    unfold dfiVoronoiMinusMultiplier dfiVoronoiPlusMultiplier
    rw [hCos]
    ring
  have hRight :
      (-(2 * Real.pi) / (q : ℂ)) *
          (2 * ((4 * Real.pi * Real.sqrt n / q : ℝ) : ℂ) ^
            (-(2 * (1 - z))) * dfiBesselY0MellinSymbol (2 * (1 - z))) =
        ((4 / (q : ℂ)) *
          (2 * ((4 * Real.pi * Real.sqrt n / q : ℝ) : ℂ) ^
            (-(2 * (1 - z))) * dfiBesselK0MellinSymbol (2 * (1 - z)))) *
          Complex.cos (Real.pi * (1 - z)) := by
    rw [hRatio]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  rw [hLeft, hPlus]
  exact hRight.symm

/-- On the interior line `Re z = 13/16`, the equal-sign Mellin--Barnes
transform is exactly DFI's literal `Y₀` transform.  The interior line is
essential: it puts `2(1-z)` in the absolute Mellin strip
`1/4 < Re s < 1/2` of the Neumann kernel. -/
theorem verticalIntegral_dfiVoronoiMinus_mellin_thirteenSixteenths_eq_bessel
    (q n : ℕ) [NeZero q] (hn : 0 < n) {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) :
    PointMean.VerticalIntegral' (fun z : ℂ =>
        (n : ℂ) ^ (-(1 - z)) * dfiVoronoiMinusMultiplier q z * mellin g z)
        (13 / 16 : ℝ) =
      dfiVoronoiMinusBesselTransform q g n := by
  let A : ℝ := 4 * Real.pi * Real.sqrt n / q
  let h : ℝ → ℂ := fun x => (dfiBesselY0 (A * Real.sqrt x) : ℂ)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : 0 < A := by dsimp [A]; positivity
  have hConv : MellinConvergent h (3 / 16 : ℂ) := by
    simpa only [h] using
      (mellinConvergent_dfiBesselY0_mul_sqrt hA
        (s := (3 / 16 : ℂ)) (by norm_num) (by norm_num))
  have hMeas : AEStronglyMeasurable h
      (volume.restrict (Set.Ioi 0)) :=
    MellinConvergent.aestronglyMeasurable_positive hConv
  have hInt : IntegrableOn (fun x : ℝ => x ^ (-(13 / 16 : ℝ)) * ‖h x‖)
      (Set.Ioi 0) := by
    simpa only [show (3 / 16 : ℂ).re - 1 = -(13 / 16 : ℝ) by norm_num] using
      MellinConvergent.integrableOn_rpow_mul_norm hConv
  have hPair := verticalIntegral'_mellin_mul_mellin_one_sub hg
    (13 / 16 : ℝ) hMeas hInt
  have hLine (u : ℝ) :
      (n : ℂ) ^ (-(1 - ((13 / 16 : ℂ) + (u : ℂ) * I))) *
            dfiVoronoiMinusMultiplier q
              ((13 / 16 : ℂ) + (u : ℂ) * I) *
            mellin g ((13 / 16 : ℂ) + (u : ℂ) * I) =
        (-(2 * Real.pi) / (q : ℂ)) *
          (mellin g ((13 / 16 : ℂ) + (u : ℂ) * I) *
            mellin h
              (1 - ((13 / 16 : ℂ) + (u : ℂ) * I))) := by
    let z : ℂ := (13 / 16 : ℂ) + (u : ℂ) * I
    have hz : 0 < (1 - z).re := by dsimp [z]; norm_num
    have hMellin := mellin_dfiBesselY0_mul_sqrt hA
      (s := 1 - z) (by dsimp [z]; norm_num) (by dsimp [z]; norm_num)
    rw [dfiVoronoiMinusMultiplier_eq_scaled_Y0_symbol q n hn z hz]
    rw [show mellin h (1 - z) =
        2 * (A : ℂ) ^ (-(2 * (1 - z))) *
          dfiBesselY0MellinSymbol (2 * (1 - z)) by simpa only [h] using hMellin]
    dsimp [z, A]
    ring
  have hKernel (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
      h x = (dfiBesselY0
        (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ) := by
    dsimp [h, A]
    congr 2
    rw [Real.sqrt_mul hx.le]
    ring
  calc
    PointMean.VerticalIntegral' (fun z : ℂ =>
        (n : ℂ) ^ (-(1 - z)) * dfiVoronoiMinusMultiplier q z * mellin g z)
        (13 / 16 : ℝ) =
      PointMean.VerticalIntegral' (fun z : ℂ =>
        (-(2 * Real.pi) / (q : ℂ)) *
          (mellin g z * mellin h (1 - z))) (13 / 16 : ℝ) :=
      verticalIntegral'_congr_line (13 / 16 : ℝ) (fun u => by
        simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hLine u)
    _ = (-(2 * Real.pi) / (q : ℂ)) *
        PointMean.VerticalIntegral' (fun z : ℂ =>
          mellin g z * mellin h (1 - z)) (13 / 16 : ℝ) := by
      rw [verticalIntegral'_const_mul_bridge]
    _ = (-(2 * Real.pi) / (q : ℂ)) *
        ∫ x : ℝ in Set.Ioi 0, g x * h x := by rw [hPair]
    _ = dfiVoronoiMinusBesselTransform q g n := by
      unfold dfiVoronoiMinusBesselTransform
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change g x * h x =
        g x * (dfiBesselY0
          (4 * Real.pi * Real.sqrt (x * n) / q) : ℂ)
      rw [hKernel x hx]


end MathCollab.Density.Stronger.Atkinson
