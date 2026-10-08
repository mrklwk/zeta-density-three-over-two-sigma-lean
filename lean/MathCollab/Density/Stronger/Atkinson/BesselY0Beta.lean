module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIY0Mellin.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselY0Abel
public import MathCollab.Density.Stronger.Atkinson.BesselK0Mellin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Arsinh

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open scoped Topology Interval

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem image_sin_Ioo_zero_halfPi :
    Real.sin '' Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxIcc : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      exact ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hx.1.le,
        hx.2.le⟩
    have hzero : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hhalf : Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [Real.pi_pos]
      · exact le_rfl
    constructor
    · simpa using Real.strictMonoOn_sin hzero hxIcc hx.1
    · simpa using Real.strictMonoOn_sin hxIcc hhalf hx.2
  · intro hy
    refine ⟨Real.arcsin y, ?_, Real.sin_arcsin (by linarith [hy.1]) hy.2.le⟩
    exact ⟨Real.arcsin_pos.2 hy.1, Real.arcsin_lt_pi_div_two.2 hy.2⟩

theorem cos_mul_one_sub_sin_sq_cpow
    (s : ℂ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Real.cos u| •
        (((1 - Real.sin u ^ 2 : ℝ) : ℂ) ^ (-(s + 1) / 2)) =
      (Real.cos u : ℂ) ^ (-s) := by
  have hneg : -(Real.pi / 2) < u :=
    (neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans_lt hu.1
  have hcos : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨hneg, hu.2⟩
  rw [abs_of_pos hcos, Complex.real_smul]
  have htrig : 1 - Real.sin u ^ 2 = Real.cos u ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [htrig]
  have hcast : (((Real.cos u ^ 2 : ℝ) : ℂ)) =
      (Real.cos u : ℂ) ^ (2 : ℕ) := by
    push_cast
    ring
  rw [hcast]
  have hC : (Real.cos u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
  rw [← Complex.cpow_nat_mul' (n := 2) (x := (Real.cos u : ℂ)) (by
      rw [Complex.arg_ofReal_of_nonneg hcos.le]
      norm_num
      exact Real.pi_pos) (by
      rw [Complex.arg_ofReal_of_nonneg hcos.le]
      norm_num
      exact Real.pi_pos.le)]
  calc
    (Real.cos u : ℂ) * (Real.cos u : ℂ) ^
        ((2 : ℂ) * (-(s + 1) / 2)) =
      (Real.cos u : ℂ) ^ (1 : ℂ) * (Real.cos u : ℂ) ^
        ((2 : ℂ) * (-(s + 1) / 2)) := by rw [Complex.cpow_one]
    _ = (Real.cos u : ℂ) ^ ((1 : ℂ) + 2 * (-(s + 1) / 2)) :=
      (Complex.cpow_add (1 : ℂ) (2 * (-(s + 1) / 2)) hC).symm
    _ = (Real.cos u : ℂ) ^ (-s) := by
      apply congrArg ((Real.cos u : ℂ) ^ ·)
      ring

theorem integral_cos_cpow_neg_eq_beta (s : ℂ) :
    (∫ u : ℝ in Set.Ioo 0 (Real.pi / 2),
        (Real.cos u : ℂ) ^ (-s)) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) ((1 - s) / 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (f := Real.sin)
    (f' := Real.cos) measurableSet_Ioo
    (fun x _ => Real.hasDerivAt_sin x |>.hasDerivWithinAt)
    (fun x hx y hy hxy => by
      exact Real.strictMonoOn_sin.injOn
        (show x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
          exact ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hx.1.le,
            hx.2.le⟩)
        (show y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
          exact ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hy.1.le,
            hy.2.le⟩) hxy)
    (fun y : ℝ => (((1 - y ^ 2 : ℝ) : ℂ) ^ (-(s + 1) / 2)))
  rw [image_sin_Ioo_zero_halfPi] at h
  calc
    (∫ u : ℝ in Set.Ioo 0 (Real.pi / 2),
        (Real.cos u : ℂ) ^ (-s)) =
        ∫ u : ℝ in Set.Ioo 0 (Real.pi / 2),
          |Real.cos u| • (((1 - Real.sin u ^ 2 : ℝ) : ℂ) ^ (-(s + 1) / 2)) := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro u hu
            exact (cos_mul_one_sub_sin_sq_cpow s hu).symm
    _ = ∫ y : ℝ in Set.Ioo 0 1,
          (((1 - y ^ 2 : ℝ) : ℂ) ^ (-(s + 1) / 2)) := h.symm
    _ = (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) ((1 - s) / 2) := by
      convert integral_one_sub_sq_cpow_Ioo_eq_half_beta (w := (1 - s) / 2) using 1
      ring_nf

theorem abs_two_mul_smul_sq_cpow_general
    (s : ℂ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |2 * x| •
        ((((x ^ 2 : ℝ) : ℂ) ^ ((1 - s) / 2 - 1)) *
          (1 - ((x ^ 2 : ℝ) : ℂ)) ^ (s / 2 - 1)) =
      2 * ((x : ℂ) ^ (-s) *
        (((1 - x ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) := by
  rw [abs_of_pos (mul_pos (by norm_num) hx.1), Complex.real_smul]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  have hcast : (((x ^ 2 : ℝ) : ℂ)) = (x : ℂ) ^ (2 : ℕ) := by
    push_cast
    ring
  rw [hcast]
  rw [← Complex.cpow_nat_mul' (n := 2) (x := (x : ℂ)) (by
      rw [Complex.arg_ofReal_of_nonneg hx.1.le]
      norm_num
      exact Real.pi_pos) (by
      rw [Complex.arg_ofReal_of_nonneg hx.1.le]
      norm_num
      exact Real.pi_pos.le)]
  calc
    ((2 * x : ℝ) : ℂ) *
          ((x : ℂ) ^ ((2 : ℂ) * ((1 - s) / 2 - 1)) *
            (1 - (x : ℂ) ^ 2) ^ (s / 2 - 1)) =
      2 * (((x : ℂ) ^ (1 : ℂ) *
          (x : ℂ) ^ ((2 : ℂ) * ((1 - s) / 2 - 1))) *
            (1 - (x : ℂ) ^ 2) ^ (s / 2 - 1)) := by
        push_cast
        rw [Complex.cpow_one]
        ring
    _ = 2 * ((x : ℂ) ^ ((1 : ℂ) + 2 * ((1 - s) / 2 - 1)) *
          (1 - (x : ℂ) ^ 2) ^ (s / 2 - 1)) := by
        rw [Complex.cpow_add (1 : ℂ) (2 * ((1 - s) / 2 - 1)) hxC]
    _ = 2 * ((x : ℂ) ^ (-s) *
          (((1 - x ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) := by
        have hone : (((1 - x ^ 2 : ℝ) : ℂ)) = 1 - (x : ℂ) ^ 2 := by
          push_cast
          ring
        rw [hone]
        congr 3
        ring

theorem integral_beta_tail_Ioo (s : ℂ) :
    (∫ x : ℝ in Set.Ioo 0 1,
        (x : ℂ) ^ (-s) * (((1 - x ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) =
      (1 / 2 : ℂ) * Complex.betaIntegral ((1 - s) / 2) (s / 2) := by
  have h := betaIntegral_square_substitution ((1 - s) / 2) (s / 2)
  have h' : Complex.betaIntegral ((1 - s) / 2) (s / 2) =
      ∫ x : ℝ in Set.Ioo 0 1,
        2 * ((x : ℂ) ^ (-s) *
          (((1 - x ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) := by
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    exact abs_two_mul_smul_sq_cpow_general s hx
  rw [h', ← MeasureTheory.integral_const_mul]
  ring_nf

theorem tanh_jacobian_beta_integrand
    (s : ℂ) {t : ℝ} (ht : 0 < t) :
    |1 / Real.cosh t ^ 2| •
        ((Real.tanh t : ℂ) ^ (-s) *
          (((1 - Real.tanh t ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) =
      (Real.sinh t : ℂ) ^ (-s) := by
  have hcosh : 0 < Real.cosh t := Real.cosh_pos t
  have htanh : 0 < Real.tanh t := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 ht) hcosh
  have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.2 ht
  rw [abs_of_pos (by positivity : 0 < 1 / Real.cosh t ^ 2), Complex.real_smul]
  rw [one_sub_tanh_sq_eq_inv_cosh_sq]
  rw [show ((1 / Real.cosh t ^ 2 : ℝ) : ℂ) *
      ((Real.tanh t : ℂ) ^ (-s) *
        (((1 / Real.cosh t ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) =
      (Real.tanh t : ℂ) ^ (-s) *
        (((1 / Real.cosh t ^ 2 : ℝ) : ℂ) *
          (((1 / Real.cosh t ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) by ring]
  rw [inv_sq_mul_inv_sq_cpow_sub_one hcosh (s / 2)]
  have hmul := Complex.mul_cpow_ofReal_nonneg htanh.le hcosh.le (-s)
  rw [show -2 * (s / 2) = -s by ring]
  rw [← hmul]
  congr 2
  norm_cast
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hcosh.ne']

theorem integral_sinh_cpow_neg_Ioi_eq_beta (s : ℂ) :
    (∫ t : ℝ in Set.Ioi 0, (Real.sinh t : ℂ) ^ (-s)) =
      (1 / 2 : ℂ) * Complex.betaIntegral ((1 - s) / 2) (s / 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.tanh)
    (f' := fun t : ℝ => 1 / Real.cosh t ^ 2) measurableSet_Ioi
    (fun t _ => (hasDerivAt_tanh_recip_cosh_sq t).hasDerivWithinAt)
    (fun x hx y hy hxy => Real.tanh_injective hxy)
    (fun y : ℝ => (y : ℂ) ^ (-s) *
      (((1 - y ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1)))
  rw [image_tanh_Ioi_zero] at h
  calc
    (∫ t : ℝ in Set.Ioi 0, (Real.sinh t : ℂ) ^ (-s)) =
        ∫ t : ℝ in Set.Ioi 0,
          |1 / Real.cosh t ^ 2| •
            ((Real.tanh t : ℂ) ^ (-s) *
              (((1 - Real.tanh t ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1))) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact (tanh_jacobian_beta_integrand s ht).symm
    _ = ∫ y : ℝ in Set.Ioo 0 1,
        (y : ℂ) ^ (-s) * (((1 - y ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1)) := h.symm
    _ = (1 / 2 : ℂ) * Complex.betaIntegral ((1 - s) / 2) (s / 2) :=
      integral_beta_tail_Ioo s

theorem image_sinh_Ioi_zero :
    Real.sinh '' Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Real.sinh_pos_iff.2 hx
  · intro hy
    exact ⟨Real.arsinh y, Real.arsinh_pos_iff.2 hy, Real.sinh_arsinh y⟩

theorem sinh_tail_jacobian
    (s : ℂ) {u : ℝ} :
    |Real.cosh u| •
        ((Real.sinh u : ℂ) ^ (-s) /
          Real.sqrt (1 + Real.sinh u ^ 2)) =
      (Real.sinh u : ℂ) ^ (-s) := by
  have hcosh : 0 < Real.cosh u := Real.cosh_pos u
  have hsqrt : Real.sqrt (1 + Real.sinh u ^ 2) = Real.cosh u := by
    rw [show 1 + Real.sinh u ^ 2 = Real.cosh u ^ 2 by
      nlinarith [Real.cosh_sq_sub_sinh_sq u], Real.sqrt_sq_eq_abs,
      abs_of_pos hcosh]
  rw [abs_of_pos hcosh, Complex.real_smul, hsqrt]
  have hcoshC : (Real.cosh u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcosh.ne'
  change (Real.cosh u : ℂ) *
      ((Real.sinh u : ℂ) ^ (-s) / (Real.cosh u : ℂ)) = _
  field_simp [hcoshC]

theorem integral_tail_power_eq_beta (s : ℂ) :
    (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (-s) / Real.sqrt (1 + t ^ 2)) =
      (1 / 2 : ℂ) * Complex.betaIntegral ((1 - s) / 2) (s / 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.sinh)
    (f' := Real.cosh) measurableSet_Ioi
    (fun u _ => Real.hasDerivAt_sinh u |>.hasDerivWithinAt)
    (fun x hx y hy hxy => Real.sinh_injective hxy)
    (fun t : ℝ => (t : ℂ) ^ (-s) / Real.sqrt (1 + t ^ 2))
  rw [image_sinh_Ioi_zero] at h
  calc
    (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (-s) / Real.sqrt (1 + t ^ 2)) =
      ∫ u : ℝ in Set.Ioi 0,
        |Real.cosh u| •
          ((Real.sinh u : ℂ) ^ (-s) /
            Real.sqrt (1 + Real.sinh u ^ 2)) := h
    _ = ∫ u : ℝ in Set.Ioi 0, (Real.sinh u : ℂ) ^ (-s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact sinh_tail_jacobian s
    _ = (1 / 2 : ℂ) * Complex.betaIntegral ((1 - s) / 2) (s / 2) :=
      integral_sinh_cpow_neg_Ioi_eq_beta s

end MathCollab.Density.Stronger.Atkinson
