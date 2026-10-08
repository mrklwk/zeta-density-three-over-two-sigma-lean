module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothBlockContour

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Uniform negligible residue before every zero and every admissible scale.
The 104th-order Mellin estimate absorbs the coarse factor sqrt(X) N^(1-β). -/
theorem smoothDetectorResidue_eventually_small {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b) :
    ∀ᶠ T : ℝ in atTop, ∀ (ρ : ℂ) (X N q : ℝ),
      3/4 ≤ ρ.re → ρ.re ≤ 1 → T ≤ |ρ.im| →
      0 ≤ X → X ≤ T → 1 ≤ N → N ≤ T^2 → 0 ≤ q →
      ‖smoothDetectorResidue ψ ρ X N q‖ ≤ T^(-100 : ℝ) := by
  obtain ⟨C,hC,h⟩ := uniform_smoothDetectorResidue_bound hψ ha hb hs 104
  filter_upwards [eventually_ge_atTop (max C 2)] with T hT
  have hCT : C ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 ≤ T := (le_max_right _ _).trans hT
  have hTp : 0 < T := by linarith
  intro ρ X N q hβ hβ' hγ hX hXT hN hNT hq
  have hNp : 0 < N := by linarith
  have hpow : N^(1-ρ.re) ≤ T^2 :=
    (Real.rpow_le_self_of_one_le hN (by linarith)).trans hNT
  have hsqrt : Real.sqrt X ≤ T := by
    apply (Real.sqrt_le_iff).2
    exact ⟨hTp.le, by nlinarith⟩
  have hnum : C*Real.sqrt X*N^(1-ρ.re) ≤ T^4 := by
    calc
      _ ≤ T*T*T^2 := mul_le_mul (mul_le_mul hCT hsqrt (Real.sqrt_nonneg _) hTp.le)
        hpow (Real.rpow_nonneg hNp.le _) (mul_nonneg hTp.le hTp.le)
      _ = T^4 := by ring
  have hden : T^104 ≤ (1+|ρ.im|)^104 :=
    pow_le_pow_left₀ hTp.le (by linarith) _
  calc
    _ ≤ C*Real.sqrt X*N^(1-ρ.re)/(1+|ρ.im|)^104 :=
      h ρ X N q hβ hβ' hX hNp hq
    _ ≤ T^4/T^104 := div_le_div₀ (by positivity) hnum (pow_pos hTp _) hden
    _ = T^(-100 : ℝ) := by
      rw [Real.rpow_neg hTp.le, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      apply (div_eq_iff (pow_ne_zero 104 hTp.ne')).2
      rw [inv_mul_eq_div]
      apply (eq_div_iff (pow_ne_zero 100 hTp.ne')).2
      rw [← pow_add]

end MathCollab.Density.Stronger
