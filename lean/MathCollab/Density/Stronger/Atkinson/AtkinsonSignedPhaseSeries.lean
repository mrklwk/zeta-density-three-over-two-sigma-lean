module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationarySeries
public import MathCollab.Density.Stronger.Atkinson.AtkinsonMainNormalization
public import MathCollab.Density.Stronger.Atkinson.AtkinsonMainVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixVectors

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonNegativePhaseTerm (T : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-1:ℂ)^n * Complex.exp ((-atkinsonSourcePhase T n : ℂ)*I)

def atkinsonPositiveMainSum (T G L : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonPositiveMainWeight T G L n * atkinsonPositivePhaseTerm T n

def atkinsonNegativeMainSum (T G L : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonNegativeMainWeight T G L n * atkinsonNegativePhaseTerm T n

def atkinsonCommonMainPhase (T : ℝ) : ℂ :=
  (1+I)*zetaSquareReflectedGammaPhase T*Complex.exp ((atkinsonCentralPhase T : ℂ)*I)

theorem atkinsonStationaryLeadingTerm_eq_signed {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (n : ℕ) :
    atkinsonStationaryLeadingTerm T G L n = atkinsonCommonMainPhase T *
      (atkinsonPositiveMainWeight T G L n*atkinsonPositivePhaseTerm T n -
        atkinsonNegativeMainWeight T G L n*atkinsonNegativePhaseTerm T n) := by
  have he : (2:ℂ)*(Real.sqrt Real.pi : ℂ)*(atkinsonBesselScale (1/4) n : ℂ) =
      (((n:ℝ)^(-(1/4:ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast atkinsonBesselScale_quarter_normalization n
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold atkinsonStationaryLeadingTerm atkinsonStationaryLeadingIntegral
  rw [atkinsonStationaryMain_sqrt_normalized hT,atkinsonStationaryMain_neg_sqrt_normalized hT hG]
  unfold atkinsonCommonMainPhase atkinsonPositiveMainWeight atkinsonNegativeMainWeight
    atkinsonPositivePhaseTerm atkinsonNegativePhaseTerm atkinsonFourthRootCoefficient
    neumannLeadingPlus neumannLeadingMinus
  push_cast
  rw [← he]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem atkinsonStationaryLeadingFiniteSum_eq_signed {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (N : ℕ) :
    atkinsonStationaryLeadingFiniteSum T G L N =
      atkinsonCommonMainPhase T *
        (atkinsonPositiveMainSum T G L N-atkinsonNegativeMainSum T G L N) := by
  unfold atkinsonStationaryLeadingFiniteSum atkinsonPositiveMainSum atkinsonNegativeMainSum
  simp_rw [atkinsonStationaryLeadingTerm_eq_signed hT hG L]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]

theorem atkinsonStationaryLeadingSum_eq_signed {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    atkinsonStationaryLeadingSum T G L =
      atkinsonCommonMainPhase T *
        (atkinsonPositiveMainSum T G L (atkinsonSourceCutoff T G L)-
          atkinsonNegativeMainSum T G L (atkinsonSourceCutoff T G L)) := by
  rw [atkinsonStationaryLeadingSum_eq_finite hT hG hL hwidth,
    atkinsonStationaryLeadingFiniteSum_eq_signed hT hG.ne']

theorem norm_atkinsonCommonMainPhase_le (T : ℝ) :
    ‖atkinsonCommonMainPhase T‖ ≤ 2 := by
  unfold atkinsonCommonMainPhase
  rw [norm_mul,norm_mul,norm_zetaSquareReflectedGammaPhase,Complex.norm_exp_ofReal_mul_I,
    mul_one,mul_one]
  apply (norm_add_le _ _).trans
  norm_num

theorem norm_atkinsonStationaryLeadingSum_le_signed {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    ‖atkinsonStationaryLeadingSum T G L‖ ≤ 2*
      (‖atkinsonPositiveMainSum T G L (atkinsonSourceCutoff T G L)‖+
        ‖atkinsonNegativeMainSum T G L (atkinsonSourceCutoff T G L)‖) := by
  rw [atkinsonStationaryLeadingSum_eq_signed hT hG hL hwidth,norm_mul]
  exact mul_le_mul (norm_atkinsonCommonMainPhase_le T) (norm_sub_le _ _)
    (norm_nonneg _) (by norm_num)

theorem atkinsonNegativePhaseTerm_eq_conj (T : ℝ) (n : ℕ) :
    atkinsonNegativePhaseTerm T n = (starRingEnd ℂ) (atkinsonPositivePhaseTerm T n) := by
  unfold atkinsonNegativePhaseTerm atkinsonPositivePhaseTerm divisorWeight
  simp only [map_mul,map_pow,map_neg,map_one,map_natCast,← Complex.exp_conj,
    Complex.conj_ofReal,Complex.conj_I]
  congr 2
  ring

end MathCollab.Density.Stronger.Atkinson
