module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction; see third_party/twelfth/ATKINSON_CORRECTION_SERIES_MANIFEST.json.
Mathlib and the nonstationary foundations retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCarrierAlgebra

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_atkinsonPowerIntegrand (T G L α b x : ℝ) :
    ‖atkinsonPowerIntegrand T G L α b x‖ =
      ‖zetaAtkinsonDivisorTest T G L x‖ * |x ^ (-α)| := by
  have he : ‖Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [atkinsonPowerIntegrand, norm_mul, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem integrable_atkinsonPowerIntegrand {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α b : ℝ) :
    Integrable (atkinsonPowerIntegrand T G L α b) := by
  let hg := zetaAtkinsonDivisorVoronoiTest hT hG hL
  have hi : Integrable (zetaAtkinsonDivisorTest T G L) :=
    hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport
  have hr : Measurable (fun x : ℝ => x ^ (-α)) := by fun_prop
  have he : Continuous (fun x : ℝ =>
      Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I)) := by fun_prop
  have hm : AEStronglyMeasurable (atkinsonPowerIntegrand T G L α b) :=
    (hg.continuous.aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp hr).aestronglyMeasurable).mul he.aestronglyMeasurable
  have hpc : ContinuousOn (fun x : ℝ => x ^ (-α)) (Icc (T / 16) T) := by
    intro x hx
    have hx0 : 0 < x := (by positivity : 0 < T / 16).trans_le hx.1
    exact (Real.continuousAt_rpow_const x (-α) (Or.inl hx0.ne')).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc
  apply (hi.norm.const_mul B).mono' hm
  apply Filter.Eventually.of_forall
  intro x
  rw [norm_atkinsonPowerIntegrand]
  by_cases hz : zetaAtkinsonDivisorTest T G L x = 0
  · simp [hz]
  have hs : x ∈ Function.support (zetaSmoothDivisorTest T G L) := by
    rw [← support_zetaAtkinsonDivisorTest]
    exact hz
  have hb := hB x (support_zetaSmoothDivisorTest_physical hT hG hL hwidth hs)
  rw [Real.norm_eq_abs] at hb
  calc
    _ ≤ ‖zetaAtkinsonDivisorTest T G L x‖ * B :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_comm _ _

def atkinsonTwoTermCarrierIntegral (T G L : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt Real.pi / Real.pi : ℂ) *
    ((atkinsonBesselScale (1 / 4) n : ℂ) *
      (neumannLeadingPlus * atkinsonPowerIntegral T G L (1 / 4) (Real.sqrt n) +
       neumannLeadingMinus * atkinsonPowerIntegral T G L (1 / 4) (-Real.sqrt n)) -
     (atkinsonBesselScale (3 / 4) n : ℂ) / 8 *
      (neumannCorrectionPlus * atkinsonPowerIntegral T G L (3 / 4) (Real.sqrt n) +
       neumannCorrectionMinus * atkinsonPowerIntegral T G L (3 / 4) (-Real.sqrt n)))

theorem integral_zetaAtkinsonTwoTermIntegrand_eq_carriers {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0, zetaAtkinsonTwoTermIntegrand T G L n x) =
      atkinsonTwoTermCarrierIntegral T G L n := by
  have h1p := (integrable_atkinsonPowerIntegrand hT hG hL hwidth
    (1 / 4) (Real.sqrt n)).integrableOn (s := Ioi 0)
  have h1m := (integrable_atkinsonPowerIntegrand hT hG hL hwidth
    (1 / 4) (-Real.sqrt n)).integrableOn (s := Ioi 0)
  have h3p := (integrable_atkinsonPowerIntegrand hT hG hL hwidth
    (3 / 4) (Real.sqrt n)).integrableOn (s := Ioi 0)
  have h3m := (integrable_atkinsonPowerIntegrand hT hG hL hwidth
    (3 / 4) (-Real.sqrt n)).integrableOn (s := Ioi 0)
  have he := setIntegral_congr_fun (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun x hx => zetaAtkinsonTwoTermIntegrand_eq_carriers
      (T := T) (G := G) (L := L) (x := x) hx hn)
  rw [he, integral_const_mul]
  have h1 : IntegrableOn (fun x => (atkinsonBesselScale (1 / 4) n : ℂ) *
      (neumannLeadingPlus * atkinsonPowerIntegrand T G L (1 / 4) (Real.sqrt n) x +
       neumannLeadingMinus * atkinsonPowerIntegrand T G L (1 / 4) (-Real.sqrt n) x)) (Ioi 0) :=
    ((h1p.const_mul neumannLeadingPlus).add (h1m.const_mul neumannLeadingMinus)).const_mul _
  have h3 : IntegrableOn (fun x => (atkinsonBesselScale (3 / 4) n : ℂ) / 8 *
      (neumannCorrectionPlus * atkinsonPowerIntegrand T G L (3 / 4) (Real.sqrt n) x +
       neumannCorrectionMinus * atkinsonPowerIntegrand T G L (3 / 4) (-Real.sqrt n) x)) (Ioi 0) :=
    ((h3p.const_mul neumannCorrectionPlus).add (h3m.const_mul neumannCorrectionMinus)).const_mul _
  rw [integral_sub h1 h3]
  rw [integral_const_mul, integral_const_mul,
    integral_add (h1p.const_mul neumannLeadingPlus) (h1m.const_mul neumannLeadingMinus),
    integral_add (h3p.const_mul neumannCorrectionPlus) (h3m.const_mul neumannCorrectionMinus)]
  simp only [integral_const_mul, atkinsonTwoTermCarrierIntegral, atkinsonPowerIntegral]

theorem zetaAtkinsonTwoTerm_eq_carrierIntegral {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (n : ℕ) :
    zetaAtkinsonTwoTerm T G L n =
      divisorWeight n * (-(2 * Real.pi) : ℂ) * atkinsonTwoTermCarrierIntegral T G L n := by
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonTwoTerm, divisorWeight]
  rw [zetaAtkinsonTwoTerm,
    integral_zetaAtkinsonTwoTermIntegrand_eq_carriers hT hG hL hwidth (Nat.pos_of_ne_zero hn)]

end MathCollab.Density.Stronger.Atkinson
