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
public import MathCollab.Density.Stronger.Atkinson.QuadraticGaussian
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSaddleGaussian (T G : ℝ) (n : ℕ) : ℂ :=
  zetaGaussianQuadraticIntegral T G
    (2 * Real.arsinh (Real.sqrt (Real.pi * (n : ℝ) / (2 * T))))

theorem third_mul_le_arsinh {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 2) : x / 3 ≤ Real.arsinh x := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => Real.arsinh z - z / 3)
      ((Real.sqrt (1 + y ^ 2))⁻¹ - 1 / 3) y :=
    (Real.hasDerivAt_arsinh y).sub ((hasDerivAt_id y).div_const 3)
  have hm : MonotoneOn (fun z : ℝ => Real.arsinh z - z / 3) (Icc 0 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    have hs : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hs3 : Real.sqrt (1 + y ^ 2) ≤ 3 :=
      (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hy.1, hy.2]⟩
    have h := one_div_le_one_div_of_le hs hs3
    simpa only [one_div] using sub_nonneg.mpr h
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 2) ⟨hx, hx2⟩ hx
  simp only [Real.arsinh_zero, zero_div, sub_zero] at h
  linarith

def quadraticFrequencyEnvelope (G v : ℝ) : ℝ := Real.exp (-(G*v)^2/8)

theorem quadraticFrequencyEnvelope_antitone (G : ℝ) :
    AntitoneOn (quadraticFrequencyEnvelope G) (Ici 0) := by
  intro a ha b hb hab
  apply Real.exp_le_exp.mpr
  have hsq : a^2 ≤ b^2 := pow_le_pow_left₀ ha hab 2
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg G)
  nlinarith

theorem norm_quadraticGaussian_increment_le {T G a b : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G^2 ≤ 2*T) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖zetaGaussianQuadraticIntegral T G b-zetaGaussianQuadraticIntegral T G a‖ ≤
      2*Real.sqrt Real.pi*G*(quadraticFrequencyEnvelope G a-quadraticFrequencyEnvelope G b) := by
  let B : ℝ → ℝ := fun v => (Real.sqrt Real.pi*G^3/2)*v*quadraticFrequencyEnvelope G v
  have hBi : IntervalIntegrable B volume a b := by
    apply Continuous.intervalIntegrable
    dsimp [B,quadraticFrequencyEnvelope]
    fun_prop
  have hprim (v : ℝ) : HasDerivAt
      (fun w => -2*Real.sqrt Real.pi*G*quadraticFrequencyEnvelope G w) (B v) v := by
    have h := (((((hasDerivAt_id v).const_mul G).pow 2).neg.div_const 8).exp).const_mul
      (-2*Real.sqrt Real.pi*G)
    convert h using 1
    · rfl
    · dsimp [B,quadraticFrequencyEnvelope]
      ring
  have hi : (∫ v in a..b, B v) =
      2*Real.sqrt Real.pi*G*(quadraticFrequencyEnvelope G a-quadraticFrequencyEnvelope G b) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hprim v) hBi]
    ring
  rw [← hi]
  apply norm_sub_le_integral_of_norm_deriv_le_of_le hab
    (fun x _ => (hasDerivAt_zetaGaussianQuadraticIntegral T hG.ne' x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_zetaGaussianQuadraticIntegral T hG.ne' x).differentiableAt.differentiableWithinAt)
    _ hBi
  exact Filter.Eventually.of_forall (fun v hv => by
    have h := norm_deriv_zetaGaussianQuadraticIntegral_le hT hG hGT v
    rwa [abs_of_nonneg (ha.trans hv.1.le)] at h)

def atkinsonSaddleFrequency (T : ℝ) (n : ℕ) : ℝ :=
  2*Real.arsinh (Real.sqrt (Real.pi*(n:ℝ)/(2*T)))

theorem atkinsonSaddleFrequency_nonneg (T : ℝ) (n : ℕ) :
    0 ≤ atkinsonSaddleFrequency T n := by
  exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _))

theorem atkinsonSaddleFrequency_monotone {T : ℝ} (hT : 0 < T) :
    Monotone (atkinsonSaddleFrequency T) := by
  intro m n hmn
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.arsinh_strictMono.monotone
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) Real.pi_pos.le

theorem finiteVariationBound_atkinsonSaddleGaussian {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G^2 ≤ 2*T) (m N : ℕ) :
    FiniteVariationBound (fun i => atkinsonSaddleGaussian T G (m+i)) N
      (2*Real.sqrt Real.pi*G*quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T m)) := by
  have hm : Monotone (fun i : ℕ => atkinsonSaddleFrequency T (m+i)) :=
    (atkinsonSaddleFrequency_monotone hT).comp (fun _ _ h => Nat.add_le_add_left h m)
  have he : AntitoneOn (fun i => quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T (m+i))) (Iic N) :=
    fun i _ j _ hij => quadraticFrequencyEnvelope_antitone G
      (atkinsonSaddleFrequency_nonneg T _) (atkinsonSaddleFrequency_nonneg T _) (hm hij)
  have h := finiteVariationBound_of_envelope
    (e := fun i => quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T (m+i)))
    (M := 2*Real.sqrt Real.pi*G) (by positivity)
    (fun i _ => (Real.exp_pos _).le) he
    (f := fun i => atkinsonSaddleGaussian T G (m+i))
    (fun i _ => by
      have h := norm_zetaGaussianQuadraticIntegral_le hT hG hGT (atkinsonSaddleFrequency T (m+i))
      change ‖atkinsonSaddleGaussian T G (m+i)‖ ≤
        Real.sqrt Real.pi*G*quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T (m+i)) at h
      have hp : 0 ≤ Real.sqrt Real.pi*G*quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T (m+i)) := by
        unfold quadraticFrequencyEnvelope
        positivity
      nlinarith)
    (fun i _ => norm_quadraticGaussian_increment_le hT hG hGT
      (atkinsonSaddleFrequency_nonneg T _) (hm (Nat.le_succ i)))
  simpa only [Nat.add_zero] using h

theorem quadraticFrequencyEnvelope_saddle_le_physical {T : ℝ}
    (hT : 0 < T) (G : ℝ) (n : ℕ) (hn : (n:ℝ) ≤ T) :
    quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T n) ≤
      Real.exp (-(G^2*(n:ℝ))/(12*T)) := by
  let x := Real.sqrt (Real.pi*(n:ℝ)/(2*T))
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by norm_num,?_⟩
    apply (div_le_iff₀ (by positivity : 0 < 2*T)).2
    nlinarith [Real.pi_lt_four,Nat.cast_nonneg (α := ℝ) n]
  have ha := third_mul_le_arsinh hx hx2
  have ha0 : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr hx
  have hxsq : x^2 = Real.pi*(n:ℝ)/(2*T) := Real.sq_sqrt (by positivity)
  have hsq : (n:ℝ)/(6*T) ≤ (Real.arsinh x)^2 := by
    have hfirst : x^2/9 ≤ (Real.arsinh x)^2 := by nlinarith
    apply le_trans _ hfirst
    rw [hxsq]
    apply (div_le_div_iff₀ (by positivity : 0 < 6*T) (by norm_num : (0:ℝ)<9)).2
    have he := (eq_div_iff (by positivity : 2*T ≠ 0)).mp hxsq
    nlinarith [Real.pi_gt_three,Nat.cast_nonneg (α := ℝ) n]
  have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg G)
  apply Real.exp_le_exp.mpr
  change -(G*(2*Real.arsinh x))^2/8 ≤ _
  calc
    _ = -(G^2*(Real.arsinh x)^2)/2 := by ring
    _ ≤ -(G^2*((n:ℝ)/(6*T)))/2 := by linarith
    _ = _ := by ring

theorem finiteVariationBound_atkinsonSaddleGaussian_physical {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G^2 ≤ 2*T) (m N : ℕ) (hm : (m:ℝ) ≤ T) :
    FiniteVariationBound (fun i => atkinsonSaddleGaussian T G (m+i)) N
      (2*Real.sqrt Real.pi*G*Real.exp (-(G^2*(m:ℝ))/(12*T))) := by
  apply (finiteVariationBound_atkinsonSaddleGaussian hT hG hGT m N).mono
  exact mul_le_mul_of_nonneg_left (quadraticFrequencyEnvelope_saddle_le_physical hT G m hm) (by positivity)

end MathCollab.Density.Stronger.Atkinson
