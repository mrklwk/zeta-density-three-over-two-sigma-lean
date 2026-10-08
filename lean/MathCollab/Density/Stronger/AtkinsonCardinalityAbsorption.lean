module
-- Reversible module-visibility port of the audited development.
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Adapted from Scott McColm, source commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
McColm source: MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
The localized packet bound remains an explicit theorem hypothesis.
No physical Atkinson estimate or point-mean theorem is imported or asserted.
-/

set_option autoImplicit false

/-!
# Cardinality absorption at an explicit physical length

This finite lemma will be consumed by the actual source packets.
The length is chosen from the packet constant and the value threshold;
the required square-root absorption is derived exactly.
-/

noncomputable section

namespace MathCollab.Density.Stronger

def atkinsonAbsorptionLength (A G Y : ℝ) : ℝ :=
  (Y^2/(4*A))^2/G

theorem atkinsonAbsorptionLength_pos {A G Y : ℝ}
    (hA : 0 < A) (hG : 0 < G) (hY : 0 < Y) :
    0 < atkinsonAbsorptionLength A G Y := by
  unfold atkinsonAbsorptionLength
  positivity

theorem atkinsonAbsorptionLength_radical {A G Y : ℝ}
    (hA : 0 < A) (hG : 0 < G) :
    Real.sqrt (G*atkinsonAbsorptionLength A G Y) = Y^2/(4*A) := by
  have he : G*atkinsonAbsorptionLength A G Y = (Y^2/(4*A))^2 := by
    unfold atkinsonAbsorptionLength
    field_simp
  rw [he,Real.sqrt_sq (by positivity)]

theorem atkinsonAbsorptionLength_absorbs {A G Y : ℝ}
    (hA : 0 < A) (hG : 0 < G) :
    2*A*Real.sqrt (G*atkinsonAbsorptionLength A G Y) ≤ Y^2 := by
  rw [atkinsonAbsorptionLength_radical hA hG]
  have he : 2*A*(Y^2/(4*A)) = Y^2/2 := by field_simp; ring
  rw [he]
  nlinarith [sq_nonneg Y]

theorem atkinson_card_le_of_packet {A H G L Y : ℝ} {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : (∑ t ∈ W, f t)^2 ≤
      A*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)))
    (habsorb : 2*A*Real.sqrt (G*L) ≤ Y^2) :
    (W.card:ℝ) ≤ 2*A*H/(G*Y^2) := by
  by_cases hW : W.Nonempty
  · have hR : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
    have hsum : (W.card:ℝ)*Y ≤ ∑ t ∈ W, f t := by
      simpa using Finset.sum_le_sum hlarge
    have hsq := (pow_le_pow_left₀ (by positivity : 0 ≤ (W.card:ℝ)*Y) hsum 2).trans hpacket
    have hhalf := mul_le_mul_of_nonneg_right habsorb (sq_nonneg (W.card:ℝ))
    have hquad : (W.card:ℝ)*((W.card:ℝ)*Y^2) ≤
        (W.card:ℝ)*(2*A*(H/G)) := by
      ring_nf at hsq hhalf ⊢
      nlinarith
    have hc := (mul_le_mul_iff_right₀ hR).mp hquad
    apply (le_div_iff₀ (mul_pos hG (sq_pos_of_pos hY))).2
    have he := (le_div_iff₀ hG).mp (show (W.card:ℝ)*Y^2 ≤ (2*A*H)/G by
      convert hc using 1; ring)
    nlinarith
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

theorem atkinson_covered_card_budget {A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y) :
    ((Nat.floor (H/atkinsonAbsorptionLength A G Y)+1:ℕ):ℝ)*
      (2*A*H/(G*Y^2)) ≤
      2*A*H/(G*Y^2)+32*A^3*H^2/Y^6 := by
  have hL := atkinsonAbsorptionLength_pos hA hG hY
  have hfloor := Nat.floor_le (div_nonneg hH hL.le)
  have hc : ((Nat.floor (H/atkinsonAbsorptionLength A G Y)+1:ℕ):ℝ) ≤
      H/atkinsonAbsorptionLength A G Y+1 := by
    push_cast
    linarith
  calc
    _ ≤ (H/atkinsonAbsorptionLength A G Y+1)*(2*A*H/(G*Y^2)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      unfold atkinsonAbsorptionLength
      field_simp
      ring

end MathCollab.Density.Stronger
