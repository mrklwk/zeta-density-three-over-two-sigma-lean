module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalizedGapBudget

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinson_far_radical_eq_rpow {H M : ℝ} (hH : 0 < H) (hM : 0 < M) (L : ℝ) :
    Real.sqrt (M*L/Real.sqrt (H*M)) = H^(-(1/4:ℝ))*M^(1/4:ℝ)*Real.sqrt L := by
  have hMpow : M/M^(1/2:ℝ) = M^(1/2:ℝ) := by
    calc
      _ = M^(1-(1/2:ℝ)) := by rw [Real.rpow_sub hM,Real.rpow_one]
      _ = _ := by norm_num
  have hbase : M/Real.sqrt (H*M) = H^(-(1/2:ℝ))*M^(1/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.mul_rpow hH.le hM.le,Real.rpow_neg hH.le]
    calc
      _ = (H^(1/2:ℝ))⁻¹*(M/M^(1/2:ℝ)) := by ring
      _ = _ := by rw [hMpow]
  have hroot : Real.sqrt (M/Real.sqrt (H*M)) = H^(-(1/4:ℝ))*M^(1/4:ℝ) := by
    rw [hbase,Real.sqrt_eq_rpow,Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hH.le,← Real.rpow_mul hM.le]
    norm_num
  calc
    _ = Real.sqrt ((M/Real.sqrt (H*M))*L) := by congr 1; ring
    _ = Real.sqrt (M/Real.sqrt (H*M))*Real.sqrt L := Real.sqrt_mul (by positivity) _
    _ = _ := by rw [hroot]

theorem atkinson_weighted_diagonal_power {M : ℝ} (hM : 0 < M) (η : ℝ) :
    M^(1/2+η)*M = M^(3/2+η) := by
  calc
    _ = M^(1/2+η)*M^(1:ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hM]; congr 1; ring

theorem atkinson_weighted_near_power {H M : ℝ} (hH : 0 < H) (hM : 0 < M) (η : ℝ) :
    M^(1/2+η)*Real.sqrt (H*M) = Real.sqrt H*M^(1+η) := by
  rw [Real.sqrt_mul hH.le,Real.sqrt_eq_rpow M]
  calc
    _ = Real.sqrt H*(M^(1/2+η)*M^(1/2:ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hM]; congr 1; congr 1; ring

theorem atkinson_weighted_far_power {H M : ℝ} (hH : 0 < H) (hM : 0 < M) (η L : ℝ) :
    M^(1/2+η)*Real.sqrt (M*L/Real.sqrt (H*M)) =
      H^(-(1/4:ℝ))*Real.sqrt L*M^(3/4+η) := by
  rw [atkinson_far_radical_eq_rpow hH hM L]
  calc
    _ = H^(-(1/4:ℝ))*Real.sqrt L*(M^(1/2+η)*M^(1/4:ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hM]; congr 1; congr 1; ring
end MathCollab.Density.Stronger.Atkinson
