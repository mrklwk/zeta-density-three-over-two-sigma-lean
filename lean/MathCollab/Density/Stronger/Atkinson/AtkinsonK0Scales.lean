module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonK0Series
public import MathCollab.Density.Stronger.Atkinson.SourceLogScales

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem besselK0_source_power_absorb {C T A : ℝ} {k : ℕ}
    (hT : 1 ≤ T) (hCT : C ≤ T) (hk : A + 2 ≤ (k : ℝ)) :
    C * T / T ^ k ≤ T ^ (-A) := by
  have hT0 : 0 < T := by linarith
  have hp : T ^ (1 - (k : ℝ)) ≤ T ^ (-A - 1) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  calc
    _ = C * T ^ (1 - (k : ℝ)) := by
      rw [Real.rpow_sub hT0, Real.rpow_one, Real.rpow_natCast]
      ring
    _ ≤ T * T ^ (-A - 1) := mul_le_mul hCT hp (Real.rpow_nonneg hT0.le _) hT0.le
    _ = T ^ (1 + (-A - 1)) := by rw [Real.rpow_add hT0, Real.rpow_one]
    _ = _ := by congr 1; ring

/-- Uniform O(G) bound for the complete literal modified-Bessel branch. -/
theorem exists_norm_zetaAtkinsonBesselPlus_le_mul_G :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G^2 ≤ 2*T →
      0 < L → 8*L ≤ G → ‖zetaAtkinsonBesselPlus T G L‖ ≤ C*G := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_zetaAtkinsonBesselPlus_le (k := 2) le_rfl
  refine ⟨C,hC,?_⟩
  intro T G L hT hG hGT hL hw
  apply (hbound T G L hT hG hGT hL hw).trans
  have hT0 : 0 < T := by linarith
  have he : C*G*T/T^2 = (C*G)/T := by field_simp
  rw [he]
  exact div_le_self (by positivity) (by linarith)

theorem exists_zetaAtkinsonBesselPlus_powerSaving {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T →
      T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselPlus T G (Real.log T)‖ ≤ G * T ^ (-A) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (A + 2)
  let k : ℕ := max 2 m
  have hk : 2 ≤ k := le_max_left _ _
  have hkA : A + 2 ≤ (k : ℝ) := hm.le.trans (by exact_mod_cast le_max_right 2 m)
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselPlus_le hk
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselPlus T G (Real.log T)‖ ≤ G * T ^ (-A) := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop C] with T hsupport hscale hTC
    intro G hlower hupper
    obtain ⟨hG, hlog, hwidth, _⟩ := hsupport.2 G hlower
    have hb := hbound T G (Real.log T) hsupport.1 hG (hscale.2.2 G hG hupper).1 hlog hwidth
    have hp := mul_le_mul_of_nonneg_left
      (besselK0_source_power_absorb (by linarith [hsupport.1]) hTC hkA) hG.le
    apply hb.trans
    convert hp using 1
    ring
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨max 16 T₁, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  exact hT₁ T ((le_max_right _ _).trans hT) G hlower hupper


end MathCollab.Density.Stronger.Atkinson
