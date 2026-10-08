module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_FINITE_ERROR_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSourceCutoffBound
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFiniteStationaryError

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex Filter
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson


theorem atkinsonStationary_scale_identity {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (q : ℝ) :
    G*Real.sqrt G*T^(-(1/2 : ℝ))*(37*T*L^2/G^2)^q =
      (37:ℝ)^q*T^(q-1/2)*L^(2*q)*G^(3/2-2*q) := by
  have hbase : (37*T*L^2/G^2)^q =
      (37:ℝ)^q*T^q*L^(2*q)/G^(2*q) := by
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity : 0 ≤ 37*T) (sq_nonneg L),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 37) hT.le,
      ← Real.rpow_natCast,← Real.rpow_mul hL.le,
      ← Real.rpow_natCast,← Real.rpow_mul hG.le]
    norm_num
  have hg : G*Real.sqrt G = G^(3/2 : ℝ) := by
    calc
      _ = G^(1:ℝ)*G^(1/2:ℝ) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hG]; norm_num
  rw [hbase,hg,Real.rpow_sub hT,Real.rpow_sub hG,Real.rpow_neg hT.le]
  ring

theorem atkinsonStationary_cutoff_scale_le {T G L q : ℝ}
    (hT : 1 ≤ T) (hG : 1 ≤ G) (hupper : G ≤ Real.sqrt T) (hL : 1 ≤ L)
    (hq : 3/4 ≤ q) (hq1 : q ≤ 1) :
    G*Real.sqrt G*T^(-(1/2 : ℝ))*
      (atkinsonSourceCutoff T G L : ℝ)^q ≤ 37*T^(q-1/2)*L^2 := by
  have hT0 : 0 < T := by linarith
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hN := atkinsonSourceCutoff_le_natural hT hG0 hupper hL
  have hmono := Real.rpow_le_rpow (Nat.cast_nonneg (atkinsonSourceCutoff T G L)) hN
    (show 0 ≤ q by linarith)
  have hGp : G^(3/2-2*q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hG (by linarith)
  have hLp : L^(2*q) ≤ L^2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h37 : (37:ℝ)^q ≤ 37 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 37) hq1
    simpa only [Real.rpow_one] using h
  calc
    _ ≤ G*Real.sqrt G*T^(-(1/2 : ℝ))*(37*T*L^2/G^2)^q :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (37:ℝ)^q*T^(q-1/2)*L^(2*q)*G^(3/2-2*q) :=
      atkinsonStationary_scale_identity hT0 hG0 hL0 q
    _ ≤ 37*T^(q-1/2)*L^2*1 := by gcongr
    _ = _ := mul_one _

end MathCollab.Density.Stronger.Atkinson
