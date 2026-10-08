module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPowerAmplitude
public import MathCollab.Density.Stronger.Atkinson.AtkinsonAmplitudeIntegral
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform cancellation for the actual power-weighted divisor source

The positive-support restriction and square change of variables are
proved for the actual phase-adjusted test. The final bound is uniform
in every real carrier parameter, including both Bessel signs.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonPowerIntegrand (T G L α b x : ℝ) : ℂ :=
  zetaAtkinsonDivisorTest T G L x * ((x ^ (-α) : ℝ) : ℂ) *
    Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I)

def atkinsonPowerIntegral (T G L α b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, atkinsonPowerIntegrand T G L α b x

theorem atkinsonPowerIntegrand_sq {T y : ℝ} (hT : 0 < T) (hy : 0 < y)
    (G L α b : ℝ) :
    (2 * y : ℝ) • atkinsonPowerIntegrand T G L α b (y ^ 2) =
      2 * (atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y) := by
  rw [atkinsonPowerWeight_eq_amplitude hT (sq_pos_of_pos hy) G L α, Real.sqrt_sq hy.le]
  have hc := zetaAtkinsonDivisorTest_mul_carrier T G L b (sq_pos_of_pos hy)
  rw [zetaAtkinsonPhase_sq T b hy] at hc
  have hp : Complex.exp (((2 * Real.pi * atkinsonRootPhase T b y : ℝ) : ℂ) * I) =
      atkinsonRootKernel T b y := by
    unfold atkinsonRootKernel
    congr 1
    push_cast
    ring
  rw [hp] at hc
  push_cast at hc
  unfold atkinsonPowerIntegrand
  simp only [real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (2 * (y : ℂ) * (((y ^ 2) ^ (-α) : ℝ) : ℂ)) * hc

theorem atkinsonPowerIntegral_eq_root {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α b : ℝ) :
    atkinsonPowerIntegral T G L α b =
      2 * ∫ y in Real.sqrt (T / 16)..Real.sqrt T,
        atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y := by
  have hab : Real.sqrt (T / 16) ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  have ha : 0 < Real.sqrt (T / 16) := Real.sqrt_pos.2 (by positivity)
  have he : atkinsonPowerIntegral T G L α b =
      ∫ x in (T / 16)..T, atkinsonPowerIntegrand T G L α b x := by
    unfold atkinsonPowerIntegral
    rw [intervalIntegral.integral_of_le (by linarith : T / 16 ≤ T),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => (by positivity : 0 < T / 16).trans_le hx.1)
    intro x hx
    have hz : zetaAtkinsonDivisorTest T G L x = 0 := by
      by_contra hn
      have hs : x ∈ Function.support (zetaSmoothDivisorTest T G L) := by
        rw [← support_zetaAtkinsonDivisorTest]
        exact hn
      exact hx.2 (support_zetaSmoothDivisorTest_physical hT hG hL hwidth hs)
    simp [atkinsonPowerIntegrand, hz]
  have hc := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := atkinsonPowerIntegrand T G L α b) (f := fun y : ℝ => y ^ 2)
    (f' := fun y : ℝ => 2 * y) (a := Real.sqrt (T / 16)) (b := Real.sqrt T)
    (by fun_prop) (fun y _ => by simpa using! (hasDerivAt_id y).pow 2)
    (fun y hy => by
      rw [min_eq_left hab, max_eq_right hab] at hy
      have := ha.trans hy.1
      positivity)
  rw [Real.sq_sqrt (by positivity : 0 ≤ T / 16), Real.sq_sqrt hT.le] at hc
  rw [he, ← hc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hab] at hy
  exact atkinsonPowerIntegrand_sq hT (ha.trans_le hy.1) G L α b

theorem exists_norm_atkinsonPowerIntegral_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
      ‖atkinsonPowerIntegral T G L α b‖ ≤ C * G * T ^ (-α) := by
  obtain ⟨C, hC, hweight⟩ := exists_intervalC1Bound_atkinsonPowerWeight α
  refine ⟨16 * C, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth
  have hab : Real.sqrt (T / 16) ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  have ha : 0 < Real.sqrt (T / 16) := Real.sqrt_pos.2 (by positivity)
  have hf : IntervalC1Bound (atkinsonPowerWeight T G L α)
      ((Real.sqrt (T / 16)) ^ 2) ((Real.sqrt T) ^ 2) (C * G * T ^ (-α)) := by
    simpa only [Real.sq_sqrt (by positivity : 0 ≤ T / 16), Real.sq_sqrt hT.le] using
      hweight T G L hT hG hGT hL
  have h := (hf.comp_sq ha.le hab).atkinsonRoot hT b ha hab
  rw [atkinsonPowerIntegral_eq_root hT hG hL hwidth α b, norm_mul, norm_ofNat]
  have hfin := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  convert hfin using 1
  ring

end MathCollab.Density.Stronger.Atkinson
