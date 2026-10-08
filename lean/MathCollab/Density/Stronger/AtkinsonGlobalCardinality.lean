module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.AtkinsonHeightCover

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
# Global cardinality from locally absorbed packets

The localization is constructed at the explicit absorption length.
The finite step is conditional on the displayed localized packet inequality.
It does not assert that the actual zeta-source packets satisfy that hypothesis.
-/

noncomputable section


namespace MathCollab.Density.Stronger

theorem atkinson_card_le_of_local_packets {A H G Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ B : ℝ, (∀ t ∈ U, B ≤ t ∧ t ≤ B+atkinsonAbsorptionLength A G Y) →
        (∑ t ∈ U, f t)^2 ≤
          A*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
            Real.sqrt (G*atkinsonAbsorptionLength A G Y))) :
    (W.card:ℝ) ≤ 2*A*H/(G*Y^2)+32*A^3*H^2/Y^6 := by
  let L := atkinsonAbsorptionLength A G Y
  have hL : 0 < L := atkinsonAbsorptionLength_pos hA hG hY
  have hfiber (k : ℕ) :
      ((atkinsonHeightFiber H L W k).card:ℝ) ≤ 2*A*H/(G*Y^2) := by
    have hsub := atkinsonHeightFiber_subset H L W k
    have hlocal := atkinsonHeightFiber_interval k hL (fun t ht => (hrange t ht).1)
    have hp := hpacket (atkinsonHeightFiber H L W k) hsub (H+(k:ℝ)*L) hlocal
    exact atkinson_card_le_of_packet hA hH hG hY
      (fun t ht => hlarge t (hsub ht)) hp (atkinsonAbsorptionLength_absorbs hA hG)
  have hcover := atkinson_card_le_of_height_fibers hL
    (fun t ht => (hrange t ht).2) (fun k _ => hfiber k)
  exact hcover.trans (atkinson_covered_card_budget hA hH hG hY)

theorem atkinson_count_exponent_budget {D H G Y ν : ℝ}
    (hD : 0 ≤ D) (hH : 1 ≤ H) (hG : 0 < G) (hY : 0 < Y) (hν : 0 ≤ ν) :
    2*(D*H^(ν/3))*H/(G*Y^2)+32*(D*H^(ν/3))^3*H^2/Y^6 ≤
      (2*D+32*D^3)*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
  have hH0 : 0 < H := by linarith
  have hpow : H^(ν/3) ≤ H^ν :=
    Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have hcube : (H^(ν/3))^3 = H^ν := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hH0.le]
    norm_num
  have he : (D*H^(ν/3))^3 = D^3*H^ν := by rw [mul_pow,hcube]
  rw [he]
  calc
    _ ≤ 2*(D*H^ν)*H/(G*Y^2)+32*(D^3*H^ν)*H^2/Y^6 := by
      apply add_le_add _ le_rfl
      gcongr
    _ ≤ _ := by
      have h1 : 0 ≤ 2*D*H^ν*(H^2/Y^6) := by positivity
      have h2 : 0 ≤ 32*D^3*H^ν*(H/(G*Y^2)) := by positivity
      ring_nf at h1 h2 ⊢
      nlinarith

end MathCollab.Density.Stronger
