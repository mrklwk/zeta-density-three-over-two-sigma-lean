module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/FOURTH_MOMENT_MANIFEST.json.
Mathlib and narrow DigammaSeries dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import MathCollab.Density.Stronger.Fourth.SquarePrefix

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open MathCollab.Density.Stronger
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth


theorem zeta_fourth_dyadic :
    ∀ η : ℝ, 0 < η → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η) := by
  intro η hη
  let q : ℝ := min η 1/20
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    have h := min_le_right η 1
    dsimp [q]
    linarith
  have hqη : 7*q ≤ η := by
    have h := min_le_left η 1
    dsimp [q]
    linarith
  obtain ⟨Kt,hKt,Ht,hHt,herror⟩ := exists_norm_fourthRightPiece_sub_cutoff_le hq
  obtain ⟨Kg,hKg,hgaussian⟩ := exists_norm_sq_fourthPrefix_le_gaussian hq
  obtain ⟨Dp,hDp,hmean⟩ := exists_integral_gaussian_fourthPolynomial_le hq
  obtain ⟨Db,hDb,hbudget⟩ := exists_fourth_dyadic_budget hq hq1
  refine ⟨8*Kg*Dp*Db+8*Kt^2,max Ht (4*q),by positivity,?_⟩
  intro H hH hH0
  have hHHt : Ht ≤ H := (le_max_left _ _).trans hH
  have hHq : 4*q ≤ H := (le_max_right _ _).trans hH
  have hH4 : 4 ≤ H := hHt.trans hHHt
  have hH1 : 1 ≤ H := by linarith
  obtain ⟨M,hNlower,hNupper⟩ := exists_dyadic_cutoff
    (Real.one_le_rpow hH1 (by positivity : 0 ≤ 1+q))
  have hNlowerNat : H^(1+q) ≤ ((2^M:ℕ):ℝ) := by exact_mod_cast hNlower
  let F : ℝ → ℝ := fun t =>
    ∫ u : ℝ, Real.exp (-98*u^2)*
      ‖dirichletPrefix (2^M) (zetaFourthCoeff q) (u-t)‖^2
  have hFnonneg (t : ℝ) : 0 ≤ F t := integral_nonneg (fun _ => by positivity)
  have hFi : IntervalIntegrable F volume H (2*H) :=
    intervalIntegrable_gaussianPrefixMean (by norm_num : (0:ℝ)<98)
      (2^M) (zetaFourthCoeff q) H (2*H)
  have hpoint : ∀ t ∈ Icc H (2*H), zetaMomentCriticalNorm t^4 ≤
      8*Kg*(2*H)^(2*q)*F t+8*Kt^2 := by
    intro t ht
    let P : ℂ := zetaFourthPrefix t q (Finset.range (2^M+1))
    have hE : ‖zetaFourthRightPiece t-P‖ ≤ Kt :=
      herror H hHHt t ht.1 ht.2 (2^M) hNlowerNat q hq
    have htri : ‖zetaFourthRightPiece t‖ ≤ ‖P‖+‖zetaFourthRightPiece t-P‖ := by
      calc
        _ = ‖P+(zetaFourthRightPiece t-P)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hEsq := pow_le_pow_left₀ (norm_nonneg _) hE 2
    have hz := zeta_fourth_le_four_mul_rightPiece_sq t
    have hsplit : zetaMomentCriticalNorm t^4 ≤ 8*‖P‖^2+8*Kt^2 := by
      nlinarith [sq_nonneg (‖P‖-‖zetaFourthRightPiece t-P‖)]
    have hPg : ‖P‖^2 ≤ Kg*t^(2*q)*F t :=
      hgaussian t (hH4.trans ht.1) (hHq.trans ht.1) (2^M)
    have ht0 : 0 ≤ t := hH0.le.trans ht.1
    have hpower := Real.rpow_le_rpow ht0 ht.2 (by positivity : 0 ≤ 2*q)
    have hP : ‖P‖^2 ≤ Kg*(2*H)^(2*q)*F t :=
      hPg.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hKg.le) (hFnonneg t))
    nlinarith
  have hFmean : (∫ t in H..2*H, F t) ≤
      Dp*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q :=
    hmean q hq.le M H hH0.le
  have hmain : (2*H)^(2*q)*((M:ℝ)+1)^2*
      (H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q ≤ Db*H^(1+7*q) :=
    hbudget H hH1 M hNupper
  have hlast : H^(1+7*q) ≤ H^(1+η) :=
    Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
  have hlinear : H ≤ H^(1+η) := by
    calc
      H = H^(1:ℝ) := (Real.rpow_one H).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
  calc
    _ ≤ ∫ t in H..2*H, 8*Kg*(2*H)^(2*q)*F t+8*Kt^2 :=
      intervalIntegral.integral_mono_on (by linarith)
        ((continuous_zetaMomentCriticalNorm.pow 4).intervalIntegrable H (2*H))
        ((hFi.const_mul _).add intervalIntegrable_const) hpoint
    _ = 8*Kg*(2*H)^(2*q)*(∫ t in H..2*H, F t)+8*Kt^2*H := by
      rw [intervalIntegral.integral_add (hFi.const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ 8*Kg*(2*H)^(2*q)*
        (Dp*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q)+8*Kt^2*H :=
      add_le_add (mul_le_mul_of_nonneg_left hFmean
        (by positivity : 0 ≤ 8*Kg*(2*H)^(2*q))) le_rfl
    _ = 8*Kg*Dp*((2*H)^(2*q)*((M:ℝ)+1)^2*
        (H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q)+8*Kt^2*H := by ring
    _ ≤ 8*Kg*Dp*(Db*H^(1+7*q))+8*Kt^2*H :=
      add_le_add (mul_le_mul_of_nonneg_left hmain
        (by positivity : 0 ≤ 8*Kg*Dp)) le_rfl
    _ = (8*Kg*Dp*Db)*H^(1+7*q)+(8*Kt^2)*H := by ring
    _ ≤ (8*Kg*Dp*Db)*H^(1+η)+(8*Kt^2)*H^(1+η) :=
      add_le_add (mul_le_mul_of_nonneg_left hlast (by positivity))
        (mul_le_mul_of_nonneg_left hlinear (by positivity))
    _ = _ := by ring



end MathCollab.Density.Stronger.Fourth
