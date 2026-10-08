module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselMellin.lean,
exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/BESSEL_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain
Apache-2.0 attribution. No Estermann or general-modulus source closure is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselK0
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.MellinTransform

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open scoped Topology Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- Mellin transform of the order-zero modified Bessel kernel. -/
noncomputable def dfiBesselK0MellinSymbol (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (s - 2) * Gamma (s / 2) ^ 2

/-- Mellin transform of the order-zero Neumann kernel. -/
noncomputable def dfiBesselY0MellinSymbol (s : ℂ) : ℂ :=
  -((2 : ℂ) ^ (s - 1) / Real.pi) *
    Complex.cos (Real.pi * s / 2) * Gamma (s / 2) ^ 2

theorem dfiBesselK0MellinSymbol_two_mul (w : ℂ) :
    dfiBesselK0MellinSymbol (2 * w) =
      (2 : ℂ) ^ (2 * w - 2) * Gamma w ^ 2 := by
  unfold dfiBesselK0MellinSymbol
  congr 2
  ring_nf

theorem dfiBesselY0MellinSymbol_two_mul (w : ℂ) :
    dfiBesselY0MellinSymbol (2 * w) =
      -((2 : ℂ) ^ (2 * w - 1) / Real.pi) *
        Complex.cos (Real.pi * w) * Gamma w ^ 2 := by
  unfold dfiBesselY0MellinSymbol
  congr 2
  · ring_nf
  · congr 1
    ring_nf

/-- The elementary Gamma integral after a positive real dilation. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x))) =
      (1 / a : ℂ) ^ s * Gamma s := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_exp] using
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hs ha

/-- Squaring is a bijection from the positive unit interval to itself. -/
theorem image_sq_Ioo_zero_one :
    (fun x : ℝ => x ^ 2) '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change 0 < x ^ 2
      exact sq_pos_of_pos hx.1
    · change x ^ 2 < 1
      nlinarith [hx.1, hx.2, sq_nonneg (x - 1)]
  · intro hy
    have hs := Real.sq_sqrt hy.1.le
    refine ⟨Real.sqrt y, ⟨Real.sqrt_pos.2 hy.1, ?_⟩, hs⟩
    nlinarith [hy.2, Real.sqrt_nonneg y]

/-- Set-integral presentation of the Euler beta integral. -/
theorem betaIntegral_eq_integral_Ioo (u v : ℂ) :
    Complex.betaIntegral u v =
      ∫ x : ℝ in Set.Ioo 0 1,
        (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-- The exact square-substitution identity behind the hyperbolic beta
integral. -/
theorem betaIntegral_square_substitution (u v : ℂ) :
    Complex.betaIntegral u v =
      ∫ x : ℝ in Set.Ioo 0 1,
        |2 * x| •
          (((x ^ 2 : ℝ) : ℂ) ^ (u - 1) *
            (1 - ((x ^ 2 : ℝ) : ℂ)) ^ (v - 1)) := by
  rw [betaIntegral_eq_integral_Ioo]
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (0 : ℝ) 1) (f := fun x : ℝ => x ^ 2)
    (f' := fun x : ℝ => 2 * x) measurableSet_Ioo
    (fun x _ => by
      convert (hasDerivAt_pow 2 x).hasDerivWithinAt using 1
      ring_nf)
    (fun x hx y hy hxy => by
      have hxp : 0 < x := hx.1
      have hyp : 0 < y := hy.1
      nlinarith)
    (fun x : ℝ =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1))
  rwa [image_sq_Ioo_zero_one] at h

/-- The Jacobian cancels the square-root singularity in the beta
substitution. -/
theorem abs_two_mul_smul_sq_cpow_neg_half
    {x : ℝ} (hx : 0 < x) :
    |2 * x| • (((x ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1)) = 2 := by
  rw [abs_of_pos (mul_pos (by norm_num) hx), Complex.real_smul]
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring]
  rw [Complex.cpow_neg]
  have hsqrt : (((x ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = x := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (sq_nonneg x)]
    norm_cast
    rw [show (x ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt (x ^ 2) by
      rw [Real.sqrt_eq_rpow], Real.sqrt_sq_eq_abs, abs_of_pos hx]
  rw [hsqrt]
  norm_num
  field_simp [hx.ne']

/-- Euler's beta integral after `u = tanh t` and then `v = u²`. -/
theorem integral_one_sub_sq_cpow_Ioo_eq_half_beta
    {w : ℂ} :
    (∫ x : ℝ in Set.Ioo 0 1,
        ((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1)) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) w := by
  have h := betaIntegral_square_substitution (1 / 2 : ℂ) w
  have h' : Complex.betaIntegral (1 / 2) w =
      ∫ x : ℝ in Set.Ioo 0 1,
        2 * (((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1)) := by
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change |2 * x| •
        ((((x ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1)) *
          (1 - ((x ^ 2 : ℝ) : ℂ)) ^ (w - 1)) = _
    rw [← smul_mul_assoc, abs_two_mul_smul_sq_cpow_neg_half hx.1]
    push_cast
    norm_num
  rw [h', ← MeasureTheory.integral_const_mul]
  ring_nf

/-- Hyperbolic tangent maps the positive half-line bijectively to the
positive unit interval. -/
theorem image_tanh_Ioi_zero :
    Real.tanh '' Set.Ioi (0 : ℝ) = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.2 hx) (Real.cosh_pos x)
    · exact Real.tanh_lt_one x
  · intro hy
    refine ⟨Real.artanh y, Real.artanh_pos hy, Real.tanh_artanh ?_⟩
    exact ⟨by linarith [hy.1], hy.2⟩

/-- The derivative of `tanh`, in the reciprocal-cosh-square form needed by
the Mellin calculation. -/
theorem hasDerivAt_tanh_recip_cosh_sq (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  have hfun : Real.sinh / Real.cosh = Real.tanh := by
    funext y
    exact (Real.tanh_eq_sinh_div_cosh (x := y)).symm
  rw [hfun] at h
  convert h using 1
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The elementary hyperbolic identity used by the `tanh` substitution. -/
theorem one_sub_tanh_sq_eq_inv_cosh_sq (x : ℝ) :
    1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- Complex-power bookkeeping for the hyperbolic Jacobian. -/
theorem inv_sq_mul_inv_sq_cpow_sub_one
    {c : ℝ} (hc : 0 < c) (w : ℂ) :
    ((1 / c ^ 2 : ℝ) : ℂ) *
        (((1 / c ^ 2 : ℝ) : ℂ) ^ (w - 1)) =
      (c : ℂ) ^ (-2 * w) := by
  let C : ℂ := (c : ℂ)
  have hC : C ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hCarg : C.arg = 0 := Complex.arg_ofReal_of_nonneg hc.le
  have hbase : (((1 / c ^ 2 : ℝ) : ℂ)) = (C ^ (2 : ℕ))⁻¹ := by
    dsimp [C]
    push_cast
    field_simp
  rw [hbase]
  have hB : (C ^ (2 : ℕ))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hC)
  calc
    (C ^ (2 : ℕ))⁻¹ * ((C ^ (2 : ℕ))⁻¹ ^ (w - 1)) =
        ((C ^ (2 : ℕ))⁻¹ ^ (w - 1)) *
          ((C ^ (2 : ℕ))⁻¹ ^ (1 : ℂ)) := by
            rw [Complex.cpow_one]
            ring
    _ = (C ^ (2 : ℕ))⁻¹ ^ ((w - 1) + 1) :=
      (Complex.cpow_add (w - 1) 1 hB).symm
    _ = (C ^ (2 : ℕ))⁻¹ ^ w := by
      congr 1
      ring
    _ = ((C ^ (2 : ℕ)) ^ w)⁻¹ := by
      have hpow : C ^ (2 : ℕ) = ((c ^ 2 : ℝ) : ℂ) := by
        simp [C]
      rw [Complex.inv_cpow]
      rw [hpow]
      rw [Complex.arg_ofReal_of_nonneg (sq_nonneg c)]
      exact Real.pi_ne_zero.symm
    _ = (C ^ (2 * w))⁻¹ := by
      congr 1
      exact (Complex.cpow_nat_mul' (n := 2) (x := C) (by
          rw [hCarg]
          norm_num
          exact Real.pi_pos) (by
          rw [hCarg]
          norm_num
          exact Real.pi_pos.le) w).symm
    _ = C ^ (-2 * w) := by
      rw [show -2 * w = -(2 * w) by ring, Complex.cpow_neg]
    _ = (c : ℂ) ^ (-2 * w) := by rfl

/-- Pointwise Jacobian identity for the hyperbolic substitution. -/
theorem tanh_jacobian_smul_one_sub_sq_cpow
    (x : ℝ) (w : ℂ) :
    (1 / Real.cosh x ^ 2) •
        (((1 - Real.tanh x ^ 2 : ℝ) : ℂ) ^ (w - 1)) =
      (Real.cosh x : ℂ) ^ (-2 * w) := by
  rw [one_sub_tanh_sq_eq_inv_cosh_sq]
  rw [Complex.real_smul]
  exact inv_sq_mul_inv_sq_cpow_sub_one (Real.cosh_pos x) w

/-- Exact beta evaluation of the hyperbolic power integral. -/
theorem integral_cosh_cpow_neg_two_mul_Ioi_eq
    (w : ℂ) :
    (∫ x : ℝ in Set.Ioi 0,
        (Real.cosh x : ℂ) ^ (-2 * w)) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) w := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.tanh)
    (f' := fun x : ℝ => 1 / Real.cosh x ^ 2) measurableSet_Ioi
    (fun x _ => (hasDerivAt_tanh_recip_cosh_sq x).hasDerivWithinAt)
    Real.tanh_injective.injOn
    (fun u : ℝ => ((1 - u ^ 2 : ℝ) : ℂ) ^ (w - 1))
  rw [image_tanh_Ioi_zero] at h
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (Real.cosh x : ℂ) ^ (-2 * w)) =
        ∫ x : ℝ in Set.Ioi 0,
          |1 / Real.cosh x ^ 2| •
            (((1 - Real.tanh x ^ 2 : ℝ) : ℂ) ^ (w - 1)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x _
              change (Real.cosh x : ℂ) ^ (-2 * w) =
                |1 / Real.cosh x ^ 2| •
                  (((1 - Real.tanh x ^ 2 : ℝ) : ℂ) ^ (w - 1))
              rw [abs_of_pos (by positivity : 0 < 1 / Real.cosh x ^ 2)]
              exact (tanh_jacobian_smul_one_sub_sq_cpow x w).symm
    _ = ∫ u : ℝ in Set.Ioo 0 1,
          ((1 - u ^ 2 : ℝ) : ℂ) ^ (w - 1) := h.symm
    _ = (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) w :=
      integral_one_sub_sq_cpow_Ioo_eq_half_beta

/-- Absolute integrability of the beta kernel obtained after the square
substitution. -/
theorem integrableOn_one_sub_sq_cpow_Ioo
    {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn
      (fun x : ℝ => ((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1))
      (Set.Ioo 0 1) := by
  let g : ℝ → ℂ := fun y =>
    (y : ℂ) ^ ((1 / 2 : ℂ) - 1) *
      (1 - (y : ℂ)) ^ (w - 1)
  have hgIoc : IntegrableOn g (Set.Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact Complex.betaIntegral_convergent (by norm_num) hw
  have hg : IntegrableOn g (Set.Ioo 0 1) :=
    hgIoc.mono_set Set.Ioo_subset_Ioc_self
  have htrans : IntegrableOn
      (fun x : ℝ => |2 * x| • g (x ^ 2)) (Set.Ioo 0 1) := by
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.Ioo (0 : ℝ) 1) (f := fun x : ℝ => x ^ 2)
      (f' := fun x : ℝ => 2 * x) measurableSet_Ioo
      (fun x _ => by
        convert (hasDerivAt_pow 2 x).hasDerivWithinAt using 1
        ring_nf)
      (fun x hx y hy hxy => by
        have hxp : 0 < x := hx.1
        have hyp : 0 < y := hy.1
        nlinarith) g
    rw [image_sq_Ioo_zero_one] at hiff
    exact hiff.mp hg
  have htwo : IntegrableOn
      (fun x : ℝ => 2 * (((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1)))
      (Set.Ioo 0 1) := by
    refine htrans.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp [g]
    change |2 * x| •
        ((((x ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1)) *
          (1 - ((x ^ 2 : ℝ) : ℂ)) ^ (w - 1)) = _
    rw [← smul_mul_assoc, abs_two_mul_smul_sq_cpow_neg_half hx.1]
    push_cast
    norm_num
  have hhalf : IntegrableOn
      (fun x : ℝ => (1 / 2 : ℂ) *
        (2 * (((1 - x ^ 2 : ℝ) : ℂ) ^ (w - 1))))
      (Set.Ioo 0 1) := htwo.const_mul (1 / 2 : ℂ)
  refine hhalf.congr_fun ?_ measurableSet_Ioo
  intro x _
  ring

/-- Absolute integrability of the hyperbolic Mellin kernel. -/
theorem integrableOn_cosh_cpow_neg_two_mul_Ioi
    {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn
      (fun x : ℝ => (Real.cosh x : ℂ) ^ (-2 * w))
      (Set.Ioi 0) := by
  let g : ℝ → ℂ := fun u =>
    ((1 - u ^ 2 : ℝ) : ℂ) ^ (w - 1)
  have hg : IntegrableOn g (Set.Ioo 0 1) :=
    integrableOn_one_sub_sq_cpow_Ioo hw
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.tanh)
    (f' := fun x : ℝ => 1 / Real.cosh x ^ 2) measurableSet_Ioi
    (fun x _ => (hasDerivAt_tanh_recip_cosh_sq x).hasDerivWithinAt)
    Real.tanh_injective.injOn g
  rw [image_tanh_Ioi_zero] at hiff
  have htrans := hiff.mp hg
  refine htrans.congr_fun ?_ measurableSet_Ioi
  intro x _
  dsimp [g]
  rw [abs_of_pos (by positivity : 0 < 1 / Real.cosh x ^ 2)]
  exact tanh_jacobian_smul_one_sub_sq_cpow x w



end MathCollab.Density.Stronger.Atkinson
