module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_WEIGHT_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonCommonSaddleFactor (T b : ℝ) : ℝ :=
  1 / (Real.sqrt 2 * Real.sqrt (Real.sqrt (b^2 + 4*(T/(2*Real.pi)))))

theorem atkinsonCommonSaddleFactor_neg (T b : ℝ) :
    atkinsonCommonSaddleFactor T (-b) = atkinsonCommonSaddleFactor T b := by
  simp only [atkinsonCommonSaddleFactor, neg_sq]

theorem atkinsonCommonSaddleFactor_pos {T : ℝ} (hT : 0 < T) (b : ℝ) :
    0 < atkinsonCommonSaddleFactor T b := by
  unfold atkinsonCommonSaddleFactor
  positivity

theorem atkinsonCommonSaddleFactor_eq_rpow {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonCommonSaddleFactor T b =
      (1/Real.sqrt 2) * (b^2+4*(T/(2*Real.pi)))^(-(1/4 : ℝ)) := by
  have hD : 0 ≤ b^2+4*(T/(2*Real.pi)) := by positivity
  have hs : Real.sqrt (Real.sqrt (b^2+4*(T/(2*Real.pi)))) =
      (b^2+4*(T/(2*Real.pi)))^(1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hD]
    norm_num
  rw [atkinsonCommonSaddleFactor,hs,Real.rpow_neg hD]
  ring

def atkinsonFourthRootCoefficient (T : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^(-(1/4:ℝ))*atkinsonCommonSaddleFactor T (Real.sqrt n)

theorem atkinsonFourthRootCoefficient_eq {T : ℝ} (hT : 0 < T) (n : ℕ) :
    atkinsonFourthRootCoefficient T n =
      (1/Real.sqrt 2)*(n:ℝ)^(-(1/4:ℝ))*
        ((n:ℝ)+2*T/Real.pi)^(-(1/4:ℝ)) := by
  rw [atkinsonFourthRootCoefficient,atkinsonCommonSaddleFactor_eq_rpow hT,
    Real.sq_sqrt (Nat.cast_nonneg n),show 4*(T/(2*Real.pi)) = 2*T/Real.pi by ring]
  ring

theorem atkinsonCommonSaddleFactor_le_height {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonCommonSaddleFactor T b ≤
      ((1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ)))*T^(-(1/4:ℝ)) := by
  have hbase : 0 < (2/Real.pi)*T := by positivity
  have hl : (2/Real.pi)*T ≤ b^2+4*(T/(2*Real.pi)) := by
    rw [show 4*(T/(2*Real.pi)) = (2/Real.pi)*T by ring]
    nlinarith [sq_nonneg b]
  rw [atkinsonCommonSaddleFactor_eq_rpow hT]
  apply (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hbase hl (by norm_num : -(1/4:ℝ) ≤ 0))
      (by positivity : 0 ≤ 1/Real.sqrt 2)).trans_eq
  rw [Real.mul_rpow (by positivity) hT.le]
  ring

theorem atkinsonFourthRootCoefficient_nonneg {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 ≤ atkinsonFourthRootCoefficient T n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (atkinsonCommonSaddleFactor_pos hT _).le

theorem atkinsonFourthRootCoefficient_le_height {T : ℝ} (hT : 0 < T) (n : ℕ) :
    atkinsonFourthRootCoefficient T n ≤
      ((1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ)))*
        T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ)) := by
  apply (mul_le_mul_of_nonneg_left (atkinsonCommonSaddleFactor_le_height hT (Real.sqrt n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans_eq
  ring

theorem atkinsonFourthRootCoefficient_antitone {T : ℝ} (hT : 0 < T) :
    AntitoneOn (atkinsonFourthRootCoefficient T) (Ici 1) := by
  intro m hm n hn hmn
  have hm0 : (0:ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmnR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have hp := Real.rpow_le_rpow_of_nonpos hm0 hmnR (by norm_num : -(1/4:ℝ) ≤ 0)
  have hq := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (m:ℝ)+2*T/Real.pi)
    (add_le_add hmnR (le_rfl : 2*T/Real.pi ≤ 2*T/Real.pi)) (by norm_num : -(1/4:ℝ) ≤ 0)
  rw [atkinsonFourthRootCoefficient_eq hT,atkinsonFourthRootCoefficient_eq hT]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hq
    (Real.rpow_nonneg (by positivity) _) (by positivity)

theorem finiteVariationBound_fourthRootCoefficient {T : ℝ} (hT : 0 < T)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    FiniteVariationBound (fun i => (atkinsonFourthRootCoefficient T (m+i) : ℂ)) N
      (((1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ)))*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))) := by
  have hanti : Antitone (fun i : ℕ => atkinsonFourthRootCoefficient T (m+i)) := by
    intro i j hij
    apply atkinsonFourthRootCoefficient_antitone hT (by simp only [mem_Ici]; omega)
      (by simp only [mem_Ici]; omega)
    omega
  have h := finiteVariationBound_of_antitone (atkinsonFourthRootCoefficient_nonneg hT m)
    (hanti.antitoneOn (Iic N)) (fun i _ => ⟨atkinsonFourthRootCoefficient_nonneg hT _,by
      simpa only [Nat.add_zero] using hanti (Nat.zero_le i)⟩)
  exact h.mono (atkinsonFourthRootCoefficient_le_height hT m)

end MathCollab.Density.Stronger.Atkinson
