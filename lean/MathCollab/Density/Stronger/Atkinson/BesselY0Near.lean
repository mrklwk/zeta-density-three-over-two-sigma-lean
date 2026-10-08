module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIBesselKernel.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselY0Bounds
public import MathCollab.Density.Stronger.Atkinson.BesselK0Mellin

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem abs_dfiBesselY0Tail_le_quarter {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0Tail x| ≤
      (1 / x) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4) := by
  have hQuarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hGammaInt := Real.integral_rpow_mul_exp_neg_mul_Ioi hQuarter hx
  have hMajorant : IntegrableOn
      (fun t : ℝ => t ^ ((1 / 4 : ℝ) - 1) * Real.exp (-(x * t)))
      (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := -(3 / 4 : ℝ)) (b := x)
      (by norm_num) (by norm_num) hx
    convert h using 1
    ext t
    norm_num
  have hTail := integrableOn_dfiBesselY0Tail_integrand hx
  have hnonneg : 0 ≤ dfiBesselY0Tail x := by
    unfold dfiBesselY0Tail
    exact integral_nonneg fun t =>
      div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  rw [abs_of_nonneg hnonneg]
  unfold dfiBesselY0Tail
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) / Real.sqrt (1 + t ^ 2) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          t ^ ((1 / 4 : ℝ) - 1) * Real.exp (-(x * t)) := by
      exact setIntegral_mono_on hTail hMajorant measurableSet_Ioi fun t ht => by
        have htPos : 0 < t := ht
        have htPowPos : 0 < t ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos htPos _
        have hsqrtPos : 0 < Real.sqrt (1 + t ^ 2) := by positivity
        have htPowLe : t ^ (3 / 4 : ℝ) ≤ Real.sqrt (1 + t ^ 2) := by
          by_cases htOne : t ≤ 1
          · have hpowOne : t ^ (3 / 4 : ℝ) ≤ 1 :=
              Real.rpow_le_one htPos.le htOne (by norm_num)
            have hsqrtOne : 1 ≤ Real.sqrt (1 + t ^ 2) := by
              have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
              nlinarith [Real.sqrt_nonneg (1 + t ^ 2), sq_nonneg t]
            exact hpowOne.trans hsqrtOne
          · have htOne' : 1 ≤ t := le_of_not_ge htOne
            have hpowT : t ^ (3 / 4 : ℝ) ≤ t := by
              simpa using Real.rpow_le_self_of_one_le htOne' (by norm_num : 3 / 4 ≤ (1 : ℝ))
            have htSqrt : t ≤ Real.sqrt (1 + t ^ 2) := by
              have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
              nlinarith [Real.sqrt_nonneg (1 + t ^ 2)]
            exact hpowT.trans htSqrt
        have hInv : 1 / Real.sqrt (1 + t ^ 2) ≤ 1 / t ^ (3 / 4 : ℝ) :=
          one_div_le_one_div_of_le htPowPos htPowLe
        rw [show t ^ ((1 / 4 : ℝ) - 1) = 1 / t ^ (3 / 4 : ℝ) by
          rw [show (1 / 4 : ℝ) - 1 = -(3 / 4 : ℝ) by ring,
            Real.rpow_neg htPos.le]
          ring]
        rw [div_eq_mul_inv, one_div]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hInv (Real.exp_pos (-x * t)).le
    _ = (1 / x) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4) := hGammaInt


end MathCollab.Density.Stronger.Atkinson
