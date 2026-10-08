module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from ZetaNeumannRemainder.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_SOURCE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannSourceBounds
public import MathCollab.Density.Stronger.Atkinson.DivisorLatticePhase

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# The Neumann expansion on the actual phase-adjusted divisor test

All kernels are composed with the literal Bessel argument. Absolute
integrability is proved before subtracting their integrals. The
complete source remainder retains the n^(-5/4) divisor weight.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonY0Integrand (T G L : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  zetaAtkinsonDivisorTest T G L x * (dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

def zetaAtkinsonTwoTermIntegrand (T G L : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  zetaAtkinsonDivisorTest T G L x * (neumannTwoTerm (4 * Real.pi * Real.sqrt (x * n)) : ℂ)

def zetaNeumannRemainderIntegrand (T G L : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  zetaAtkinsonDivisorTest T G L x *
    ((dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) -
      neumannTwoTerm (4 * Real.pi * Real.sqrt (x * n)) : ℝ) : ℂ)

theorem integrable_zetaAtkinson_kernel_of_support_bound {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (n : ℕ)
    {K : ℝ → ℝ} (hK : Measurable K) {B : ℝ}
    (hbound : ∀ x ∈ Function.support (zetaSmoothDivisorTest T G L),
      |K (4 * Real.pi * Real.sqrt (x * n))| ≤ B) :
    Integrable (fun x : ℝ => zetaAtkinsonDivisorTest T G L x *
      (K (4 * Real.pi * Real.sqrt (x * n)) : ℂ)) := by
  have hg := zetaAtkinsonDivisorVoronoiTest hT hG hL
  have hi : Integrable (zetaAtkinsonDivisorTest T G L) :=
    hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport
  have hm : Measurable (fun x : ℝ => (K (4 * Real.pi * Real.sqrt (x * n)) : ℂ)) :=
    Complex.measurable_ofReal.comp (hK.comp (by fun_prop))
  apply (hi.norm.const_mul B).mono' (hg.continuous.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  by_cases hz : zetaAtkinsonDivisorTest T G L x = 0
  · simp [hz]
  have hs : x ∈ Function.support (zetaSmoothDivisorTest T G L) := by
    rw [← support_zetaAtkinsonDivisorTest]
    exact hz
  rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖zetaAtkinsonDivisorTest T G L x‖ * B :=
      mul_le_mul_of_nonneg_left (hbound x hs) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem integrable_zetaAtkinsonY0Integrand {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) : Integrable (zetaAtkinsonY0Integrand T G L n) := by
  apply integrable_zetaAtkinson_kernel_of_support_bound (by linarith : 0 < T) hG hL n
    measurable_dfiBesselY0 (B := 7)
  intro x hx
  exact abs_dfiBesselY0_source_le_seven hT
    (support_zetaSmoothDivisorTest_physical (by linarith) hG hL hwidth hx).1 hn

theorem integrable_zetaNeumannRemainderIntegrand {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) : Integrable (zetaNeumannRemainderIntegrand T G L n) := by
  apply integrable_zetaAtkinson_kernel_of_support_bound (by linarith : 0 < T) hG hL n
    (measurable_dfiBesselY0.sub measurable_neumannTwoTerm)
    (B := neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ)))
  intro x hx
  exact abs_neumann_source_remainder_le hT
    (support_zetaSmoothDivisorTest_physical (by linarith) hG hL hwidth hx).1 hn

theorem zetaAtkinsonTwoTermIntegrand_eq_sub (T G L : ℝ) (n : ℕ) (x : ℝ) :
    zetaAtkinsonTwoTermIntegrand T G L n x =
      zetaAtkinsonY0Integrand T G L n x - zetaNeumannRemainderIntegrand T G L n x := by
  unfold zetaAtkinsonTwoTermIntegrand zetaAtkinsonY0Integrand zetaNeumannRemainderIntegrand
  push_cast
  ring

theorem integrable_zetaAtkinsonTwoTermIntegrand {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) : Integrable (zetaAtkinsonTwoTermIntegrand T G L n) := by
  have h := (integrable_zetaAtkinsonY0Integrand hT hG hL hwidth hn).sub
    (integrable_zetaNeumannRemainderIntegrand hT hG hL hwidth hn)
  convert h using 1
  funext x
  exact zetaAtkinsonTwoTermIntegrand_eq_sub T G L n x

theorem norm_integral_zetaNeumannRemainder_le {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) :
    ‖∫ x : ℝ in Ioi 0, zetaNeumannRemainderIntegrand T G L n x‖ ≤
      (neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) *
        ∫ x : ℝ in Ioi 0, ‖zetaSmoothDivisorTest T G L x‖ := by
  have hT0 : 0 < T := by linarith
  have hi := ((integrable_zetaSmoothDivisorTest hT0 hG hL).norm.integrableOn
    (s := Ioi 0)).const_mul
      (neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ)))
  have hb (x : ℝ) : ‖zetaNeumannRemainderIntegrand T G L n x‖ ≤
      (neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) *
        ‖zetaSmoothDivisorTest T G L x‖ := by
    by_cases hz : zetaSmoothDivisorTest T G L x = 0
    · simp [zetaNeumannRemainderIntegrand, zetaAtkinsonDivisorTest, hz]
    have hs := support_zetaSmoothDivisorTest_physical hT0 hG hL hwidth hz
    rw [zetaNeumannRemainderIntegrand, norm_mul, norm_zetaAtkinsonDivisorTest,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖zetaSmoothDivisorTest T G L x‖ *
          (neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (abs_neumann_source_remainder_le hT hs.1 hn) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have h := norm_integral_le_of_norm_le hi (Eventually.of_forall hb)
  simpa only [integral_const_mul] using h

theorem exists_norm_integral_zetaNeumannRemainder_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ, 0 < n →
        ‖∫ x : ℝ in Ioi 0, zetaNeumannRemainderIntegrand T G L n x‖ ≤
          C * G * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨C, hC, hmass⟩ := exists_integral_norm_zetaSmoothDivisorTest_le
  refine ⟨neumannTwoTermErrorConstant * C, mul_pos neumannTwoTermErrorConstant_pos hC, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  apply (norm_integral_zetaNeumannRemainder_le hT hG hL hwidth hn).trans
  have hfac : 0 ≤ neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) *
      (n : ℝ) ^ (-(5 / 4 : ℝ)) :=
    mul_nonneg (mul_nonneg neumannTwoTermErrorConstant_pos.le (by positivity)) (by positivity)
  calc
    _ ≤ (neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) *
        (C * G * T) :=
      mul_le_mul_of_nonneg_left (hmass T G L hT hG hGT hL hwidth) hfac
    _ = (neumannTwoTermErrorConstant * C * G * (n : ℝ) ^ (-(5 / 4 : ℝ))) *
        (T * T ^ (-(5 / 4 : ℝ))) := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (neumann_source_height_absorb (by linarith : 1 ≤ T))
        (show 0 ≤ neumannTwoTermErrorConstant * C * G * (n : ℝ) ^ (-(5 / 4 : ℝ)) from by
          exact mul_nonneg (mul_nonneg (mul_nonneg neumannTwoTermErrorConstant_pos.le hC.le) hG.le)
            (by positivity))
      simpa only [mul_one] using h

end MathCollab.Density.Stronger.Atkinson
