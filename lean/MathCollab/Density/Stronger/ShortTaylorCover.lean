module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.ShortFixedFamily

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Original smooth scale, half choice, and Taylor index: all chosen from a
finite set before the zero. -/
def smoothTaylorIndices (σ T : ℝ) : Finset (ℤ × ℕ × ℕ) :=
  (smoothScaleIndices (detectorY σ T*(Real.log T)^2)).product
    ((Finset.range 2).product (Finset.range (detectorTaylorCutoff T+1)))

def smoothTaylorMember (σ δ T : ℝ) (p : ℤ × ℕ × ℕ) (t : ℝ) : ℂ :=
  genericTaylorPolynomial
    (smoothShortCoefficient (detectorX δ T) (detectorY σ T) ((2 : ℝ)^p.1))
    (smoothHalfScale p.1 p.2.1) p.2.2 t

theorem smoothTaylorIndices_card_le_log {σ T : ℝ}
    (hD : ((smoothScaleIndices (detectorY σ T*(Real.log T)^2)).card : ℝ) ≤ 6*Real.log T)
    (hlog : 1 ≤ Real.log T) :
    ((smoothTaylorIndices σ T).card : ℝ) ≤ 144*(Real.log T)^2 := by
  have hJ := detectorTaylorCutoff_le_log hlog
  have h0 : 0 ≤ Real.log T := by linarith
  calc
    _ = ((smoothScaleIndices (detectorY σ T*(Real.log T)^2)).card : ℝ)*
        (2*(detectorTaylorCutoff T+1 : ℕ)) := by simp [smoothTaylorIndices]
    _ ≤ (6*Real.log T)*(2*(12*Real.log T)) := by push_cast; gcongr
    _ = _ := by ring

theorem shortTaylor_cutoff_error_eventually :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ 1 ≤ Real.log T ∧
      3*T^(-1 : ℝ) ≤ 1/(96*Real.log T) := by
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at ht
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1/288 by norm_num))] with T hT hlog hh
  refine ⟨hT, hlog, ?_⟩
  have hTpos : 0 < T := by linarith
  have hlo : Real.log T < T/288 := (div_lt_iff₀ hTpos).mp hh |>.trans_eq (by ring)
  rw [Real.rpow_neg_one]
  apply (le_div_iff₀ (by positivity : 0 < 96*Real.log T)).mpr
  have he : 3*T⁻¹*(96*Real.log T) = (288*Real.log T)/T := by ring
  rw [he]
  exact (div_le_one hTpos).mpr (by linarith)

/-- The detected short block produces a member of a fixed finite family;
only the selected index depends on rho. -/
theorem smooth_short_Taylor_cover {σ δ : ℝ} (hσ : 3/4 < σ) :
    ∀ᶠ T : ℝ in atTop, ∀ (ρ : ℂ) (j : ℤ),
      σ ≤ ρ.re → ρ.re ≤ 1 →
      j ∈ smoothScaleIndices (detectorY σ T*(Real.log T)^2) →
      detectorX δ T/2 < (2 : ℝ)^j →
      (2 : ℝ)^j ≤ T^(smoothingExponent σ/2) →
      (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY σ T) j‖ →
      ∃ p ∈ smoothTaylorIndices σ T, p.1 = j ∧
        detectorX δ T/4 ≤ (smoothHalfScale p.1 p.2.1 : ℝ) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ) ≤ T^(smoothingExponent σ/2) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ)^σ/(192*Real.log T) ≤
          ‖smoothTaylorMember σ δ T p ρ.im‖ := by
  filter_upwards [shortTaylor_cutoff_error_eventually] with T hsc
  obtain ⟨hT, hlog, hsmall⟩ := hsc
  intro ρ j hβ hβ' hj hlo hhi hblock
  have hTpos : 0 < T := by linarith
  have hc := smoothingExponent_lt_one hσ
  have hN : (2 : ℝ)^j ≤ T^2 := hhi.trans (by
    rw [← Real.rpow_natCast T 2]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num; linarith))
  have hY : 0 < detectorY σ T := Real.rpow_pos_of_pos hTpos _
  have hD : 0 < 24*Real.log T := by positivity
  have hs : 3*T^(-1 : ℝ) ≤ 1/(4*(24*Real.log T)) := by convert hsmall using 1; ring
  obtain ⟨hjpos, e, he, r, hr, hh⟩ := exists_smoothBlock_Taylor_member hY hT hD
    (by linarith : 0 ≤ ρ.re) hβ' hN hs hblock
  have hscale := smoothHalfScale_bounds hjpos (Finset.mem_range.mp he)
  refine ⟨(j,e,r), Finset.mem_product.mpr ⟨hj, Finset.mem_product.mpr ⟨he, hr⟩⟩,
    rfl, ?_, hscale.2.trans hhi, ?_⟩
  · change detectorX δ T/4 ≤ (smoothHalfScale j e : ℝ)
    linarith
  · have hp : (smoothHalfScale j e : ℝ)^σ ≤ (smoothHalfScale j e : ℝ)^ρ.re :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast smoothHalfScale_pos j e) hβ
    have hb := div_le_div_of_nonneg_right hp (show 0 ≤ 192*Real.log T by positivity)
    change (smoothHalfScale j e : ℝ)^σ/(192*Real.log T) ≤ _
    unfold smoothTaylorMember
    exact hb.trans (by convert hh using 1; ring)

/-- Every actual slab zero lies in the long smooth-block case or is detected
by the fixed short Taylor family, with no moment premise. -/
theorem smooth_long_or_short_Taylor_cover {σ δ : ℝ}
    (hσ : 3/4 < σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      (∃ j ∈ smoothScaleIndices (detectorY σ T*(Real.log T)^2),
        T^(smoothingExponent σ/2) < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY σ T) j‖) ∨
      (∃ p ∈ smoothTaylorIndices σ T,
        detectorX δ T/4 ≤ (smoothHalfScale p.1 p.2.1 : ℝ) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ) ≤ T^(smoothingExponent σ/2) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ)^σ/(192*Real.log T) ≤
          ‖smoothTaylorMember σ δ T p ρ.im‖) := by
  filter_upwards [smoothDetector_eventually_large hσ hδ hδ', smooth_short_Taylor_cover (δ := δ) hσ]
    with T hdet hshort
  intro ρ hβ hβ' hγ hγ' hzero
  obtain ⟨j, hj, hlo, hh⟩ := hdet ρ hβ hβ' hγ hγ' hzero
  by_cases hs : (2 : ℝ)^j ≤ T^(smoothingExponent σ/2)
  · obtain ⟨p, hp, _, hp0, hp1, hp2⟩ := hshort ρ j hβ hβ'.le hj hlo hs hh
    exact Or.inr ⟨p, hp, hp0, hp1, hp2⟩
  · exact Or.inl ⟨j, hj, lt_of_not_ge hs, hh⟩

end MathCollab.Density.Stronger
