module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/FOURTH_MOMENT_MANIFEST.json.
Mathlib and narrow DigammaSeries dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.SquareTerm

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open MathCollab.Density.Stronger
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
theorem integral_zetaFourthTerm_vertical_eq_of_le
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ) :
    (∫ u : ℝ, zetaFourthTerm t n ((a:ℂ)+(u:ℂ)*I)) =
      ∫ u : ℝ, zetaFourthTerm t n ((b:ℂ)+(u:ℂ)*I) := by
  have hbottom := tendsto_zetaFourthTerm_horizontal_of_sq_eq ha hab ht n
    (fun H => -H) (fun H => neg_sq H)
  have htop := tendsto_zetaFourthTerm_horizontal_of_sq_eq ha hab ht n
    (fun H => H) (fun _ => rfl)
  have hleft := intervalIntegral_tendsto_integral
    (integrable_zetaFourthTerm_vertical ht ha n) tendsto_neg_atTop_atBot tendsto_id
  have hright := intervalIntegral_tendsto_integral
    (integrable_zetaFourthTerm_vertical ht (ha.trans_le hab) n)
    tendsto_neg_atTop_atBot tendsto_id
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hzero :
      (0:ℂ)-0 + I • (∫ u : ℝ, zetaFourthTerm t n ((b:ℂ)+(u:ℂ)*I)) -
        I • (∫ u : ℝ, zetaFourthTerm t n ((a:ℂ)+(u:ℂ)*I)) = 0 := by
    apply tendsto_nhds_unique hlimit
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)).congr'
    apply Eventually.of_forall
    intro H
    simpa only [Complex.ofReal_neg,id_eq] using
      (zetaFourthTerm_boundaryRect_zero t n (H := H) ha hab).symm
  simp only [sub_self,zero_add,smul_eq_mul,← mul_sub] at hzero
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left I_ne_zero)).symm

theorem integral_zetaFourthTerm_vertical_eq
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) (n : ℕ) :
    (∫ u : ℝ, zetaFourthTerm t n ((a:ℂ)+(u:ℂ)*I)) =
      ∫ u : ℝ, zetaFourthTerm t n ((b:ℂ)+(u:ℂ)*I) := by
  rcases le_total a b with hab | hba
  · exact integral_zetaFourthTerm_vertical_eq_of_le ha hab ht n
  · exact (integral_zetaFourthTerm_vertical_eq_of_le hb hba ht n).symm

def zetaFourthContribution (t c : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ u : ℝ, zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)

theorem zetaFourthContribution_one (t : ℝ) (n : ℕ) :
    zetaFourthContribution t 1 n =
      zetaSquareDivisorContribution (-t) n / zetaSquareGammaNormalization t := by
  simp only [zetaFourthContribution,Complex.ofReal_one,zetaFourthTerm_one,
    integral_div,zetaSquareDivisorContribution]
  ring

theorem zetaFourthContribution_line_eq
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) (n : ℕ) :
    zetaFourthContribution t a n = zetaFourthContribution t b n := by
  rw [zetaFourthContribution,zetaFourthContribution,
    integral_zetaFourthTerm_vertical_eq ha hb ht n]

theorem hasSum_zetaFourthContribution {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    HasSum (zetaFourthContribution t c) (zetaFourthRightPiece t) := by
  have h := (hasSum_zetaSquareDivisorContribution (-t)).div_const
    (zetaSquareGammaNormalization t)
  have heq : zetaFourthContribution t c =
      fun n => zetaSquareDivisorContribution (-t) n / zetaSquareGammaNormalization t := by
    funext n
    rw [zetaFourthContribution_line_eq hc (by norm_num : (0:ℝ)<1) ht n,
      zetaFourthContribution_one]
  rw [heq,zetaFourthRightPiece]
  exact h

theorem zetaFourthRightPiece_eq_tsum {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    zetaFourthRightPiece t = ∑' n : ℕ, zetaFourthContribution t c n :=
  (hasSum_zetaFourthContribution ht hc).tsum_eq.symm



end MathCollab.Density.Stronger.Fourth
