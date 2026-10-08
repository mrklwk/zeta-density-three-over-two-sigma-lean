module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIY0PhysicalMellin.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselY0Beta
public import MathCollab.Density.Stronger.Atkinson.BesselY0Near

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter
open scoped Topology Interval

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem probe_dfiBesselY0Osc_eq_integral_sin_real (x : ℝ) :
    dfiBesselY0Osc x =
      ∫ u in (0 : ℝ)..Real.pi / 2, Real.sin (x * Real.cos u) := by
  let F : ℝ → ℂ := fun u => Complex.exp (I * (x * Real.cos u))
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hFInt : IntegrableOn F (Set.Ioc 0 (Real.pi / 2)) :=
    (hFcont.continuousOn.integrableOn_Icc (μ := volume)).mono_set
      Set.Ioc_subset_Icc_self
  have him := integral_im hFInt
  change (∫ u in Set.Ioc (0 : ℝ) (Real.pi / 2), (F u).im) =
      (∫ u in Set.Ioc (0 : ℝ) (Real.pi / 2), F u).im at him
  unfold dfiBesselY0Osc
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  calc
    (∫ u in Set.Ioc (0 : ℝ) (Real.pi / 2), F u).im =
        ∫ u in Set.Ioc (0 : ℝ) (Real.pi / 2), (F u).im := him.symm
    _ = ∫ u in Set.Ioc (0 : ℝ) (Real.pi / 2),
        Real.sin (x * Real.cos u) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp [F]
      rw [show I * ((x : ℂ) * Real.cos u) =
          (((x * Real.cos u : ℝ) : ℂ)) * I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_im (x * Real.cos u)

theorem probe_dfiBesselY0Osc_eq_integral_sin (x : ℝ) :
    (dfiBesselY0Osc x : ℂ) =
      ∫ u in (0 : ℝ)..Real.pi / 2, (Real.sin (x * Real.cos u) : ℂ) := by
  rw [probe_dfiBesselY0Osc_eq_integral_sin_real, intervalIntegral.integral_ofReal]

theorem probe_abs_dfiBesselY0Osc_le_halfPi (x : ℝ) :
    |dfiBesselY0Osc x| ≤ Real.pi / 2 := by
  rw [probe_dfiBesselY0Osc_eq_integral_sin_real]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (C := (1 : ℝ)) (f := fun u : ℝ => Real.sin (x * Real.cos u))
    (fun u _ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_sin_le_one _)
  simp only [one_mul, sub_zero, Real.norm_eq_abs] at h
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at h
  exact h

theorem probe_aestronglyMeasurable_dfiBesselY0Osc :
    AEStronglyMeasurable (fun x : ℝ => (dfiBesselY0Osc x : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
  let F : ℝ × ℝ → ℂ := fun p => (Real.sin (p.1 * Real.cos p.2) : ℂ)
  have hF : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) := by
    rw [Measure.prod_restrict]
    exact (by fun_prop : Continuous F).aestronglyMeasurable
  have hInt := hF.integral_prod_right'
  refine hInt.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  dsimp [F]
  rw [probe_dfiBesselY0Osc_eq_integral_sin,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]

theorem probe_aestronglyMeasurable_dfiBesselY0Tail :
    AEStronglyMeasurable (fun x : ℝ => (dfiBesselY0Tail x : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (Real.exp (-p.1 * p.2) / Real.sqrt (1 + p.2 ^ 2) : ℝ)
  have hF : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict]
    have hreal : Continuous (fun p : ℝ × ℝ =>
        Real.exp (-p.1 * p.2) / Real.sqrt (1 + p.2 ^ 2)) := by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro p
        exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
    exact (Complex.continuous_ofReal.comp hreal).aestronglyMeasurable
  have hInt := hF.integral_prod_right'
  refine hInt.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  dsimp [F]
  unfold dfiBesselY0Tail
  exact integral_ofReal

theorem probe_aestronglyMeasurable_dfiBesselY0 :
    AEStronglyMeasurable (fun x : ℝ => (dfiBesselY0 x : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
  unfold dfiBesselY0
  have hsub := probe_aestronglyMeasurable_dfiBesselY0Osc.sub
    probe_aestronglyMeasurable_dfiBesselY0Tail
  convert hsub.const_mul (((2 / Real.pi : ℝ) : ℂ)) using 1
  ext x
  push_cast
  simp only [Pi.sub_apply]

theorem probe_abs_dfiBesselY0_le_quarter_near
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    |dfiBesselY0 x| ≤
      (2 / Real.pi) * (Real.pi / 2 + Real.Gamma (1 / 4)) *
        (1 / x) ^ (1 / 4 : ℝ) := by
  have hosc := probe_abs_dfiBesselY0Osc_le_halfPi x
  have htail := abs_dfiBesselY0Tail_le_quarter hx.1
  have hone : 1 ≤ (1 / x) ^ (1 / 4 : ℝ) := by
    have hinv : 1 ≤ 1 / x := (le_div_iff₀ hx.1).2 (by simpa using hx.2)
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hinv
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa using h
  have hpi : 0 ≤ 2 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
  unfold dfiBesselY0
  rw [abs_mul, abs_of_nonneg hpi]
  calc
    (2 / Real.pi) * |dfiBesselY0Osc x - dfiBesselY0Tail x| ≤
        (2 / Real.pi) * (|dfiBesselY0Osc x| + |dfiBesselY0Tail x|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _ |>.trans (by simp)) hpi
    _ ≤ (2 / Real.pi) *
        (Real.pi / 2 + (1 / x) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4)) := by
      gcongr
    _ ≤ (2 / Real.pi) * (Real.pi / 2 + Real.Gamma (1 / 4)) *
        (1 / x) ^ (1 / 4 : ℝ) := by
      have hgamma : 0 ≤ Real.Gamma (1 / 4) :=
        (Real.Gamma_pos_of_pos (by norm_num)).le
      rw [show (2 / Real.pi) * (Real.pi / 2 + Real.Gamma (1 / 4)) *
          (1 / x) ^ (1 / 4 : ℝ) =
        (2 / Real.pi) * ((Real.pi / 2 + Real.Gamma (1 / 4)) *
          (1 / x) ^ (1 / 4 : ℝ)) by ring]
      apply mul_le_mul_of_nonneg_left _ hpi
      nlinarith [Real.pi_pos]

theorem probe_mellinConvergent_dfiBesselY0
    {s : ℂ} (hsLower : (1 / 4 : ℝ) < s.re)
    (hsUpper : s.re < 1 / 2) :
    MellinConvergent (fun x : ℝ => (dfiBesselY0 x : ℂ)) s := by
  let C : ℝ := (2 / Real.pi) *
    (Real.pi / 2 + Real.Gamma (1 / 4))
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s - 1) * (dfiBesselY0 x : ℂ)
  have hpowMeas : AEStronglyMeasurable (fun x : ℝ =>
      (x : ℂ) ^ (s - 1)) (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    exact ContinuousAt.continuousWithinAt
      ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx)).comp
        Complex.continuous_ofReal.continuousAt)
  have hfMeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioi 0)) :=
    hpowMeas.mul probe_aestronglyMeasurable_dfiBesselY0
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le)
      (add_nonneg (by positivity) (Real.Gamma_pos_of_pos (by norm_num)).le)
  have hsmallBase : IntegrableOn
      (fun x : ℝ => C * x ^ (s.re - 5 / 4)) (Set.Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by linarith)).const_mul C
  have hsmallMeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hfMeas.mono_measure (Measure.restrict_mono_set volume
      (show Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0 from Set.Ioc_subset_Ioi_self))
  have hsmall : IntegrableOn f (Set.Ioc 0 1) := by
    refine hsmallBase.mono' hsmallMeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    dsimp [f]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
      show (s - 1).re = s.re - 1 by simp,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      x ^ (s.re - 1) * |dfiBesselY0 x| ≤
          x ^ (s.re - 1) *
            (C * (1 / x) ^ (1 / 4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [C, mul_assoc] using
            (probe_abs_dfiBesselY0_le_quarter_near hx)
        · exact Real.rpow_nonneg hx.1.le _
      _ = C * x ^ (s.re - 5 / 4) := by
        have hinvPow : (1 / x) ^ (1 / 4 : ℝ) = x ^ (-1 / 4 : ℝ) := by
          rw [one_div, Real.inv_rpow hx.1.le, ← Real.rpow_neg hx.1.le]
          congr 1
          ring
        rw [hinvPow]
        rw [show x ^ (s.re - 1) * (C * x ^ (-1 / 4 : ℝ)) =
          C * (x ^ (s.re - 1) * x ^ (-1 / 4 : ℝ)) by ring,
          ← Real.rpow_add hx.1]
        congr 2
        ring
  have hfarBase : IntegrableOn
      (fun x : ℝ => 7 * x ^ (s.re - 3 / 2)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul 7
  have hfarMeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hfMeas.mono_measure (Measure.restrict_mono_set volume
      (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
  have hfar : IntegrableOn f (Set.Ioi 1) := by
    refine hfarBase.mono' hfarMeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxPos : 0 < x := zero_lt_one.trans hx
    dsimp [f]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
      show (s - 1).re = s.re - 1 by simp,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      x ^ (s.re - 1) * |dfiBesselY0 x| ≤
          x ^ (s.re - 1) * (7 / Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (abs_dfiBesselY0_le_seven_div_sqrt hxPos)
          (Real.rpow_nonneg hxPos.le _)
      _ = 7 * x ^ (s.re - 3 / 2) := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv,
          ← Real.rpow_neg hxPos.le]
        rw [show x ^ (s.re - 1) * (7 * x ^ (-(1 / 2 : ℝ))) =
          7 * (x ^ (s.re - 1) * x ^ (-(1 / 2 : ℝ))) by ring,
          ← Real.rpow_add hxPos]
        congr 2
        ring
  unfold MellinConvergent
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    integrableOn_union]
  exact ⟨hsmall, hfar⟩

theorem probe_tendsto_damped_dfiBesselY0_mellin
    {s : ℂ} (hsLower : (1 / 4 : ℝ) < s.re)
    (hsUpper : s.re < 1 / 2) :
    Tendsto (fun n : ℕ =>
        ∫ x : ℝ in Set.Ioi 0,
          (x : ℂ) ^ (s - 1) *
            Real.exp (-(1 / ((n : ℝ) + 1)) * x) *
            (dfiBesselY0 x : ℂ)) atTop
      (𝓝 (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselY0 x : ℂ))) := by
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s - 1) * (dfiBesselY0 x : ℂ)
  let F : ℕ → ℝ → ℂ := fun n x =>
    f x * Real.exp (-(1 / ((n : ℝ) + 1)) * x)
  have hfInt : Integrable f (volume.restrict (Set.Ioi 0)) :=
    probe_mellinConvergent_dfiBesselY0 hsLower hsUpper
  have hFMeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    exact hfInt.aestronglyMeasurable.mul
      (by fun_prop : Continuous (fun x : ℝ =>
        ((Real.exp (-(1 / ((n : ℝ) + 1)) * x) : ℝ) : ℂ))).aestronglyMeasurable
  have hBound : ∀ n, ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖F n x‖ ≤ ‖f x‖ := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply mul_le_of_le_one_right (norm_nonneg _)
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (one_div_nonneg.mpr (by positivity))) hx.le
  have hLim : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have heps : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop
        (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have harg : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1)) * x) atTop
        (𝓝 0) := by
      convert heps.neg.mul_const x using 1
      ring_nf
    have hexp : Tendsto
        (fun n : ℕ => (Real.exp (-(1 / ((n : ℝ) + 1)) * x) : ℂ)) atTop
        (𝓝 1) := by
      have hreal := Real.continuous_exp.continuousAt.tendsto.comp harg
      have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      change Tendsto
        (fun n : ℕ => (Real.exp (-(1 / ((n : ℝ) + 1)) * x) : ℂ)) atTop
        (𝓝 ((Real.exp 0 : ℝ) : ℂ)) at hcast
      simpa using hcast
    simpa only [F, mul_one] using (tendsto_const_nhds.mul hexp)
  have h := tendsto_integral_of_dominated_convergence
    (fun x : ℝ => ‖f x‖) hFMeas hfInt.norm hBound hLim
  refine h.congr' (Eventually.of_forall fun n => ?_)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp [F, f]
  ring

theorem probe_integrableOn_cos_cpow_neg_Ioc
    {s : ℂ} (hsUpper : s.re < 1) :
    IntegrableOn (fun u : ℝ => (Real.cos u : ℂ) ^ (-s))
      (Set.Ioc 0 (Real.pi / 2)) := by
  let g : ℝ → ℂ := fun y =>
    (((1 - y ^ 2 : ℝ) : ℂ) ^ (-(s + 1) / 2))
  have hw : 0 < ((1 - s) / 2).re := by
    simp only [div_re, sub_re, one_re]
    norm_num
    linarith
  have hg : IntegrableOn g (Set.Ioo 0 1) := by
    convert integrableOn_one_sub_sq_cpow_Ioo (w := (1 - s) / 2) hw using 1
    ext y
    dsimp [g]
    congr 2
    ring
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
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
            hy.2.le⟩) hxy) g
  rw [image_sin_Ioo_zero_halfPi] at hiff
  have htrans := hiff.mp hg
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  refine htrans.congr_fun ?_ measurableSet_Ioo
  intro u hu
  dsimp [g]
  exact cos_mul_one_sub_sin_sq_cpow s hu

theorem probe_integrableOn_cos_rpow_neg_Ioc
    {r : ℝ} (hrUpper : r < 1) :
    IntegrableOn (fun u : ℝ => Real.cos u ^ (-r))
      (Set.Ioc 0 (Real.pi / 2)) := by
  have hcomplex := probe_integrableOn_cos_cpow_neg_Ioc
    (s := (r : ℂ)) (by simpa using hrUpper)
  rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hcomplex ⊢
  have hnorm : IntegrableOn
      (fun u : ℝ => ‖(Real.cos u : ℂ) ^ (-(r : ℂ))‖)
      (Set.Ioo 0 (Real.pi / 2)) := hcomplex.norm
  refine hnorm.congr_fun ?_ measurableSet_Ioo
  intro u hu
  have hneg : -(Real.pi / 2) < u :=
    (neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans_lt hu.1
  have hcos : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨hneg, hu.2⟩
  change ‖(Real.cos u : ℂ) ^ (-(r : ℂ))‖ = Real.cos u ^ (-r)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hcos]
  simp

theorem probe_integrableOn_tail_rpow_div_sqrt
    {r : ℝ} (hr : 0 < r) (hrUpper : r < 1) :
    IntegrableOn (fun t : ℝ =>
      t ^ (-r) / Real.sqrt (1 + t ^ 2)) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    integrableOn_union]
  constructor
  · have hbase : IntegrableOn (fun t : ℝ => t ^ (-r)) (Set.Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
        (by linarith)
    refine hbase.mono' ?_ ?_
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
      intro t ht
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.div
      · exact Real.continuousAt_rpow_const t (-r) (Or.inl ht.1.ne')
      · fun_prop
      · exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (Real.rpow_nonneg ht.1.le _) (Real.sqrt_nonneg _))]
      have hsqrt : 1 ≤ Real.sqrt (1 + t ^ 2) := by
        have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
        nlinarith [Real.sqrt_nonneg (1 + t ^ 2)]
      exact (div_le_iff₀ (Real.sqrt_pos.2 (by positivity))).2
        (by nlinarith [Real.rpow_nonneg ht.1.le (-r)])
  · have hbase : IntegrableOn (fun t : ℝ => t ^ (-r - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hbase.mono' ?_ ?_
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.div
      · exact Real.continuousAt_rpow_const t (-r)
          (Or.inl (zero_lt_one.trans ht).ne')
      · fun_prop
      · exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htPos : 0 < t := zero_lt_one.trans ht
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (Real.rpow_nonneg htPos.le _) (Real.sqrt_nonneg _))]
      have hsqrt : t ≤ Real.sqrt (1 + t ^ 2) := by
        have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
        nlinarith [Real.sqrt_nonneg (1 + t ^ 2)]
      calc
        t ^ (-r) / Real.sqrt (1 + t ^ 2) ≤ t ^ (-r) / t :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg htPos.le _)
            htPos hsqrt
        _ = t ^ (-r - 1) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one t, ← Real.rpow_add htPos]
          congr 1

theorem probe_tendsto_damped_tail_factor
    {s : ℂ} (hs : 0 < s.re) (hsUpper : s.re < 1) :
    Tendsto (fun n : ℕ =>
        ∫ t : ℝ in Set.Ioi 0,
          (((1 / ((n : ℝ) + 1)) + t : ℝ) : ℂ) ^ (-s) /
            Real.sqrt (1 + t ^ 2)) atTop
      (𝓝 (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (-s) / Real.sqrt (1 + t ^ 2))) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → ℝ → ℂ := fun n t =>
    (((ε n + t : ℝ) : ℂ) ^ (-s)) / Real.sqrt (1 + t ^ 2)
  let f : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (-s) / Real.sqrt (1 + t ^ 2)
  let bound : ℝ → ℝ := fun t =>
    t ^ (-s.re) / Real.sqrt (1 + t ^ 2)
  have hboundInt : Integrable bound (volume.restrict (Set.Ioi 0)) :=
    probe_integrableOn_tail_rpow_div_sqrt hs hsUpper
  have hFMeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div
    · exact ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2
          (add_pos (by dsimp [ε]; positivity) ht))).comp
        Complex.continuous_ofReal.continuousAt).comp
          (continuousAt_const.add continuousAt_id)
    · fun_prop
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have hBound : ∀ n, ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ‖F n t‖ ≤ bound t := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hε : 0 < ε n := by dsimp [ε]; positivity
    have hsum : 0 < ε n + t := add_pos hε ht
    have hsqrt : 0 < Real.sqrt (1 + t ^ 2) := by positivity
    dsimp [F, bound]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hsum,
      show (-s).re = -s.re by simp,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith)) hsqrt.le
  have heps : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hLim : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => F n t) atTop (𝓝 (f t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hbase : Tendsto (fun n => ((ε n + t : ℝ) : ℂ)) atTop
        (𝓝 (t : ℂ)) := by
      have hreal : Tendsto (fun n => ε n + t) atTop (𝓝 t) := by
        simpa using heps.add_const t
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    have hpow : Tendsto
        (fun n => ((ε n + t : ℝ) : ℂ) ^ (-s)) atTop
        (𝓝 ((t : ℂ) ^ (-s))) :=
      (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 ht)).tendsto.comp hbase
    have hden : Tendsto (fun _n : ℕ =>
        ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)) := tendsto_const_nhds
    exact hpow.div hden (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.2 (by positivity))))
  have h := tendsto_integral_of_dominated_convergence
    bound hFMeas hboundInt hBound hLim
  simpa only [F, f, ε, bound] using h

theorem probe_norm_damped_sineFactor_le
    (s : ℂ) (hs : 0 ≤ s.re) {ε c : ℝ} (hc : 0 < c) :
    ‖(((ε : ℂ) - I * c) ^ (-s) -
        ((ε : ℂ) + I * c) ^ (-s)) / (2 * I)‖ ≤
      Real.exp (Real.pi * |s.im|) * c ^ (-s.re) := by
  let K : ℝ := Real.exp (Real.pi * |s.im|)
  have hbaseBound : ∀ z : ℂ, |z.im| = c → c ≤ ‖z‖ := by
    intro z hz
    rw [← hz]
    exact Complex.abs_im_le_norm z
  have hpowBound : ∀ z : ℂ, |z.im| = c →
      ‖z ^ (-s)‖ ≤ K * c ^ (-s.re) := by
    intro z hzIm
    have hnorm := hbaseBound z hzIm
    have hz : z ≠ 0 := by
      intro hz0
      rw [hz0, norm_zero] at hnorm
      linarith
    have hnum : ‖z‖ ^ (-s.re) ≤ c ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos hc hnorm (neg_nonpos.mpr hs)
    have harg : -(Complex.arg z * (-s).im) ≤ Real.pi * |s.im| := by
      rw [show (-s).im = -s.im by simp]
      calc
        -(Complex.arg z * -s.im) = Complex.arg z * s.im := by ring
        _ ≤ |Complex.arg z * s.im| := le_abs_self _
        _ = |Complex.arg z| * |s.im| := abs_mul _ _
        _ ≤ Real.pi * |s.im| := mul_le_mul_of_nonneg_right
          (Complex.abs_arg_le_pi z) (abs_nonneg _)
    rw [Complex.norm_cpow_of_ne_zero hz, div_eq_mul_inv,
      ← Real.exp_neg]
    dsimp [K]
    calc
      ‖z‖ ^ (-s).re * Real.exp (-(Complex.arg z * (-s).im)) ≤
          c ^ (-s.re) * Real.exp (Real.pi * |s.im|) := by
        apply mul_le_mul
        · simpa using hnum
        · exact Real.exp_le_exp.mpr harg
        · positivity
        · positivity
      _ = Real.exp (Real.pi * |s.im|) * c ^ (-s.re) := by ring
  have hminusIm : |(((ε : ℂ) - I * c).im)| = c := by
    simp [abs_of_pos hc]
  have hplusIm : |(((ε : ℂ) + I * c).im)| = c := by
    simp [abs_of_pos hc]
  rw [norm_div, norm_mul, norm_ofNat, Complex.norm_I]
  simp only [mul_one]
  calc
    ‖((ε : ℂ) - I * c) ^ (-s) - ((ε : ℂ) + I * c) ^ (-s)‖ / 2 ≤
        (‖((ε : ℂ) - I * c) ^ (-s)‖ +
          ‖((ε : ℂ) + I * c) ^ (-s)‖) / 2 := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (K * c ^ (-s.re) + K * c ^ (-s.re)) / 2 := by
      gcongr
      · exact hpowBound _ hminusIm
      · exact hpowBound _ hplusIm
    _ = Real.exp (Real.pi * |s.im|) * c ^ (-s.re) := by
      dsimp [K]
      ring

theorem probe_tendsto_damped_osc_factor
    {s : ℂ} (hs : 0 < s.re) (hsUpper : s.re < 1) :
    Tendsto (fun n : ℕ =>
        ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
          ((((1 / ((n : ℝ) + 1) : ℝ) : ℂ) - I * Real.cos u) ^ (-s) -
            (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) + I * Real.cos u) ^ (-s)) /
              (2 * I)) atTop
      (𝓝 (∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
        (Real.cos u : ℂ) ^ (-s) *
          Complex.sin (Real.pi * s / 2))) := by
  simp only [integral_Ioc_eq_integral_Ioo]
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → ℝ → ℂ := fun n u =>
    ((((ε n : ℝ) : ℂ) - I * Real.cos u) ^ (-s) -
      (((ε n : ℝ) : ℂ) + I * Real.cos u) ^ (-s)) / (2 * I)
  let f : ℝ → ℂ := fun u =>
    (Real.cos u : ℂ) ^ (-s) * Complex.sin (Real.pi * s / 2)
  let K : ℝ := Real.exp (Real.pi * |s.im|)
  let bound : ℝ → ℝ := fun u => K * Real.cos u ^ (-s.re)
  have hboundInt : Integrable bound
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    have hcos := probe_integrableOn_cos_rpow_neg_Ioc (r := s.re) hsUpper
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hcos
    exact hcos.const_mul K
  have hFMeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    intro n
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    intro u hu
    have hε : 0 < ε n := by dsimp [ε]; positivity
    have hminus : ((ε n : ℂ) - I * Real.cos u) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hε))
    have hplus : ((ε n : ℂ) + I * Real.cos u) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hε))
    have hminusCont : ContinuousAt
        (fun v : ℝ => ((ε n : ℂ) - I * Real.cos v)) u := by fun_prop
    have hplusCont : ContinuousAt
        (fun v : ℝ => ((ε n : ℂ) + I * Real.cos v)) u := by fun_prop
    have hminusPow : ContinuousAt (fun z : ℂ => z ^ (-s))
        ((ε n : ℂ) - I * Real.cos u) := continuousAt_cpow_const hminus
    have hplusPow : ContinuousAt (fun z : ℂ => z ^ (-s))
        ((ε n : ℂ) + I * Real.cos u) := continuousAt_cpow_const hplus
    dsimp [F]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div
    · apply ContinuousAt.sub
      · exact Filter.Tendsto.comp hminusPow hminusCont
      · exact Filter.Tendsto.comp hplusPow hplusCont
    · fun_prop
    · norm_num
  have hBound : ∀ n, ∀ᵐ u ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ‖F n u‖ ≤ bound u := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hneg : -(Real.pi / 2) < u :=
      (neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans_lt hu.1
    have hcos : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨hneg, hu.2⟩
    dsimp [F, bound, K]
    exact probe_norm_damped_sineFactor_le s hs.le hcos
  have heps : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hepsWithin : Tendsto ε atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨heps, Eventually.of_forall (fun n =>
      show 0 < ε n by dsimp [ε]; positivity)⟩
  have hLim : ∀ᵐ u ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      Tendsto (fun n => F n u) atTop (𝓝 (f u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hneg : -(Real.pi / 2) < u :=
      (neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans_lt hu.1
    have hcos : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨hneg, hu.2⟩
    have hlim := (tendsto_dfiDampedSineFactor s hcos).comp hepsWithin
    have heq := dfiDampedSineFactor_limit_eq s hcos
    dsimp [F, f]
    rw [← heq]
    exact hlim
  have h := tendsto_integral_of_dominated_convergence
    bound hFMeas hboundInt hBound hLim
  simpa only [F, f, ε, bound, K] using h

theorem probe_integrableOn_damped_osc_joint
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
          Real.sin (p.1 * Real.cos p.2))
      (Set.Ioi 0 ×ˢ Set.Ioc 0 (Real.pi / 2)) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
      Real.sin (p.1 * Real.cos p.2)
  let G : ℝ × ℝ → ℝ := fun p =>
    p.1 ^ (s.re - 1) * Real.exp (-ε * p.1) * 1
  have hxInt : IntegrableOn
      (fun x : ℝ => x ^ (s.re - 1) * Real.exp (-ε * x)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := s.re - 1) (b := ε)
      (by linarith) (by norm_num) hε
    convert h using 1
    ext x
    simp
  have huInt : IntegrableOn (fun _u : ℝ => (1 : ℝ))
      (Set.Ioc 0 (Real.pi / 2)) := by
    exact (continuous_const.integrableOn_Icc (μ := volume)).mono_set
      Set.Ioc_subset_Icc_self
  have hG : Integrable G
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) := by
    simpa [G] using hxInt.mul_prod huInt
  have hFmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) := by
    rw [Measure.prod_restrict]
    apply ContinuousOn.aestronglyMeasurable _
      (measurableSet_Ioi.prod measurableSet_Ioc)
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact ((continuousAt_cpow_const
          (Complex.ofReal_mem_slitPlane.2 hp.1)).comp
            Complex.continuous_ofReal.continuousAt).comp continuousAt_fst
      · fun_prop
    · fun_prop
  have hFG : ∀ᵐ p ∂((volume.restrict (Set.Ioi 0)).prod
      (volume.restrict (Set.Ioc 0 (Real.pi / 2)))), ‖F p‖ ≤ G p := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
    dsimp [F, G]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp.1]
    rw [show (s - 1).re = s.re - 1 by simp]
    have hExp : ‖((Real.exp (-ε * p.1) : ℝ) : ℂ)‖ =
        Real.exp (-ε * p.1) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hExp, Complex.norm_real, Real.norm_eq_abs]
    have hSin : |Real.sin (p.1 * Real.cos p.2)| ≤ 1 := Real.abs_sin_le_one _
    have hnonneg : 0 ≤ p.1 ^ (s.re - 1) * Real.exp (-ε * p.1) :=
      mul_nonneg (Real.rpow_nonneg hp.1.le _) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hSin hnonneg
  have hF : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) :=
    hG.mono' hFmeas hFG
  simpa only [F, Measure.prod_restrict] using! hF

theorem probe_integrableOn_eps_add_rpow_div_sqrt
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ =>
      (1 / (ε + t)) ^ r / Real.sqrt (1 + t ^ 2)) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    integrableOn_union]
  constructor
  · have hcont : ContinuousOn (fun t : ℝ =>
        (1 / (ε + t)) ^ r / Real.sqrt (1 + t ^ 2)) (Set.Icc 0 1) := by
      apply ContinuousOn.div
      · apply ContinuousOn.rpow_const
        apply ContinuousOn.div continuousOn_const
          (continuousOn_const.add continuousOn_id)
        intro t ht
        exact ne_of_gt (add_pos_of_pos_of_nonneg hε ht.1)
        intro t ht
        exact Or.inr hr.le
      · exact Real.continuous_sqrt.comp_continuousOn
          (continuousOn_const.add (continuousOn_id.pow 2))
      · intro t ht
        exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
    exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · have hpowInt : IntegrableOn (fun t : ℝ => t ^ (-r - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hpowInt.mono' ?_ ?_
    · exact ((continuousOn_of_forall_continuousAt fun t ht => by
          apply ContinuousAt.div
          · apply ContinuousAt.rpow_const
            · exact continuousAt_const.div
                (continuousAt_const.add continuousAt_id)
                (ne_of_gt (add_pos hε (zero_lt_one.trans ht)))
            · left
              exact ne_of_gt (one_div_pos.mpr (add_pos hε (zero_lt_one.trans ht)))
          · exact Real.continuous_sqrt.continuousAt.comp
              ((continuousAt_const.add (continuousAt_id.pow 2)))
          · exact ne_of_gt (Real.sqrt_pos.2 (by positivity))).aestronglyMeasurable
            measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htPos : 0 < t := zero_lt_one.trans ht
      have hsumPos : 0 < ε + t := add_pos hε htPos
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (Real.rpow_nonneg (one_div_nonneg.mpr hsumPos.le) _) (Real.sqrt_nonneg _))]
      have hinv : 1 / (ε + t) ≤ 1 / t := by
        exact one_div_le_one_div_of_le htPos (by linarith)
      have hpow : (1 / (ε + t)) ^ r ≤ t ^ (-r) := by
        calc
          (1 / (ε + t)) ^ r ≤ (1 / t) ^ r :=
            Real.rpow_le_rpow (by positivity) hinv hr.le
          _ = t ^ (-r) := by
            rw [one_div, Real.inv_rpow htPos.le, ← Real.rpow_neg htPos.le]
      have hsqrt : t ≤ Real.sqrt (1 + t ^ 2) := by
        have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
        nlinarith [Real.sqrt_nonneg (1 + t ^ 2)]
      have hinvSqrt : 1 / Real.sqrt (1 + t ^ 2) ≤ 1 / t :=
        one_div_le_one_div_of_le htPos hsqrt
      calc
        (1 / (ε + t)) ^ r / Real.sqrt (1 + t ^ 2) =
            (1 / (ε + t)) ^ r * (1 / Real.sqrt (1 + t ^ 2)) := by ring
        _ ≤ t ^ (-r) * (1 / t) :=
          mul_le_mul hpow hinvSqrt (by positivity) (Real.rpow_nonneg htPos.le _)
        _ = t ^ (-r - 1) := by
          rw [one_div, ← Real.rpow_neg_one t, ← Real.rpow_add htPos]
          congr 1

theorem probe_integrableOn_damped_tail_joint
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
          (Real.exp (-p.1 * p.2) / Real.sqrt (1 + p.2 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
      (Real.exp (-p.1 * p.2) / Real.sqrt (1 + p.2 ^ 2))
  let H : ℝ × ℝ → ℝ := fun p =>
    p.1 ^ (s.re - 1) * Real.exp (-(ε + p.2) * p.1) /
      Real.sqrt (1 + p.2 ^ 2)
  have hHmeas : AEStronglyMeasurable H
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict]
    apply ContinuousOn.aestronglyMeasurable _
      (measurableSet_Ioi.prod measurableSet_Ioi)
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div
    · apply ContinuousAt.mul
      · exact (Real.continuousAt_rpow_const
          p.1 (s.re - 1) (Or.inl hp.1.ne')).comp continuousAt_fst
      · fun_prop
    · exact Real.continuous_sqrt.continuousAt.comp
        (continuousAt_const.add (continuousAt_snd.pow 2))
    · exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hH : Integrable H
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    refine (integrable_prod_iff' hHmeas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change IntegrableOn (fun x : ℝ => H (x, t)) (Set.Ioi 0)
      have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := s.re - 1) (b := ε + t)
        (by linarith) (by norm_num) (add_pos hε ht)
      have hdiv : IntegrableOn (fun x : ℝ =>
          (x ^ (s.re - 1) * Real.exp (-(ε + t) * x ^ (1 : ℝ))) /
            Real.sqrt (1 + t ^ 2)) (Set.Ioi 0) :=
        hbase.div_const (Real.sqrt (1 + t ^ 2))
      exact hdiv.congr_fun (fun x hx => by
        dsimp [H]
        congr 2
        simp) measurableSet_Ioi
    · have hout : IntegrableOn (fun t : ℝ =>
          ((1 / (ε + t)) ^ s.re / Real.sqrt (1 + t ^ 2)) *
            Real.Gamma s.re) (Set.Ioi 0) :=
        (probe_integrableOn_eps_add_rpow_div_sqrt hs hε).mul_const
          (Real.Gamma s.re)
      refine hout.congr_fun ?_ measurableSet_Ioi
      intro t ht
      have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi hs (add_pos hε ht)
      have hgamma' : (∫ x in Set.Ioi (0 : ℝ),
          x ^ (s.re - 1) * Real.exp (-(ε + t) * x)) =
          (1 / (ε + t)) ^ s.re * Real.Gamma s.re := by
        convert hgamma using 1
        ring_nf
      have hnonneg : ∀ x ∈ Set.Ioi (0 : ℝ),
          0 ≤ x ^ (s.re - 1) * Real.exp (-(ε + t) * x) /
            Real.sqrt (1 + t ^ 2) := by
        intro x hx
        exact div_nonneg
          (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)
          (Real.sqrt_nonneg _)
      dsimp [H]
      calc
        ((1 / (ε + t)) ^ s.re / Real.sqrt (1 + t ^ 2)) *
              Real.Gamma s.re =
            ((1 / (ε + t)) ^ s.re * Real.Gamma s.re) /
              Real.sqrt (1 + t ^ 2) := by ring
        _ = (∫ x in Set.Ioi (0 : ℝ),
              x ^ (s.re - 1) * Real.exp (-(ε + t) * x)) /
              Real.sqrt (1 + t ^ 2) := by
            rw [hgamma']
        _ = ∫ x in Set.Ioi (0 : ℝ),
              (x ^ (s.re - 1) * Real.exp (-(ε + t) * x)) /
                Real.sqrt (1 + t ^ 2) := by
            rw [MeasureTheory.integral_div]
        _ = ∫ x in Set.Ioi (0 : ℝ),
              |x ^ (s.re - 1) * Real.exp (-(ε + t) * x) /
                Real.sqrt (1 + t ^ 2)| := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact (abs_of_nonneg (hnonneg x hx)).symm
  have hFmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict]
    apply ContinuousOn.aestronglyMeasurable _
      (measurableSet_Ioi.prod measurableSet_Ioi)
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact ((continuousAt_cpow_const
          (Complex.ofReal_mem_slitPlane.2 hp.1)).comp
            Complex.continuous_ofReal.continuousAt).comp continuousAt_fst
      · fun_prop
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have hFH : ∀ᵐ p ∂((volume.restrict (Set.Ioi 0)).prod
      (volume.restrict (Set.Ioi 0))), ‖F p‖ ≤ H p := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    dsimp [F, H]
    have hsqrtPos : 0 < Real.sqrt (1 + p.2 ^ 2) := by positivity
    have hnormSqrt :
        ‖((Real.sqrt (1 + p.2 ^ 2) : ℝ) : ℂ)‖ =
          Real.sqrt (1 + p.2 ^ 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrtPos]
    have hnormExpEps :
        ‖((Real.exp (-ε * p.1) : ℝ) : ℂ)‖ = Real.exp (-ε * p.1) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hnormExpTail :
        ‖((Real.exp (-p.1 * p.2) : ℝ) : ℂ)‖ = Real.exp (-p.1 * p.2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp.1]
    rw [show (s - 1).re = s.re - 1 by simp]
    rw [hnormExpEps, norm_div, hnormExpTail, hnormSqrt]
    apply le_of_eq
    have hexp : Real.exp (-ε * p.1) * Real.exp (-p.1 * p.2) =
        Real.exp (-(ε + p.2) * p.1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  have hF : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) :=
    hH.mono' hFmeas hFH
  simpa only [F, Measure.prod_restrict] using! hF

set_option maxHeartbeats 800000 in
theorem probe_integral_cpow_mul_damped_y0Osc_Ioi
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
          (dfiBesselY0Osc x : ℂ)) =
      (∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
          (((ε : ℂ) - I * Real.cos u) ^ (-s) -
              ((ε : ℂ) + I * Real.cos u) ^ (-s)) / (2 * I)) *
        Gamma s := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
      Real.sin (p.1 * Real.cos p.2)
  have hjointOn : IntegrableOn F
      (Set.Ioi 0 ×ˢ Set.Ioc 0 (Real.pi / 2)) :=
    probe_integrableOn_damped_osc_joint hs hε
  have hjoint : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) := by
    simpa only [F, Measure.prod_restrict] using! hjointOn
  have hswap :
      (∫ x : ℝ in Set.Ioi 0,
          ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2), F (x, u)) =
        ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
          ∫ x : ℝ in Set.Ioi 0, F (x, u) :=
    integral_integral_swap hjoint
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
          (dfiBesselY0Osc x : ℂ)) =
        ∫ x : ℝ in Set.Ioi 0,
          ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2), F (x, u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change (x : ℂ) ^ (s - 1) * ↑(Real.exp (-ε * x)) *
          ↑(dfiBesselY0Osc x) =
        ∫ u in Set.Ioc 0 (Real.pi / 2), F (x, u)
      rw [probe_dfiBesselY0Osc_eq_integral_sin,
        intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      rw [← MeasureTheory.integral_const_mul]
    _ = ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
          ∫ x : ℝ in Set.Ioi 0, F (x, u) := hswap
    _ = ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
          ((((ε : ℂ) - I * Real.cos u) ^ (-s) -
              ((ε : ℂ) + I * Real.cos u) ^ (-s)) / (2 * I) * Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u _
      simpa only [F, mul_comm] using
        (integral_cpow_mul_damped_sin_Ioi hs hε (a := Real.cos u))
    _ = (∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
          (((ε : ℂ) - I * Real.cos u) ^ (-s) -
              ((ε : ℂ) + I * Real.cos u) ^ (-s)) / (2 * I)) *
        Gamma s := by
      rw [MeasureTheory.integral_mul_const]

theorem probe_integral_cpow_mul_damped_y0Tail_Ioi
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
          (dfiBesselY0Tail x : ℂ)) =
      (∫ t : ℝ in Set.Ioi 0,
          ((ε + t : ℝ) : ℂ) ^ (-s) /
            Real.sqrt (1 + t ^ 2)) * Gamma s := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
      (Real.exp (-p.1 * p.2) / Real.sqrt (1 + p.2 ^ 2))
  have hjointOn : IntegrableOn F (Set.Ioi 0 ×ˢ Set.Ioi 0) :=
    probe_integrableOn_damped_tail_joint hs hε
  have hjoint : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    simpa only [F, Measure.prod_restrict] using! hjointOn
  have hswap :
      (∫ x : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0, F (x, t)) =
        ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0, F (x, t) :=
    integral_integral_swap hjoint
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
          (dfiBesselY0Tail x : ℂ)) =
        ∫ x : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0, F (x, t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change (x : ℂ) ^ (s - 1) * ↑(Real.exp (-ε * x)) *
          ↑(dfiBesselY0Tail x) =
        ∫ t in Set.Ioi 0, F (x, t)
      unfold dfiBesselY0Tail
      have htailCast :
          ↑(∫ t in Set.Ioi (0 : ℝ),
              Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)) =
            ∫ t in Set.Ioi (0 : ℝ),
              (↑(Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)) : ℂ) := by
        exact integral_ofReal.symm
      rw [htailCast]
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp [F]
      push_cast
      ring
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0, F (x, t) := hswap
    _ = ∫ t : ℝ in Set.Ioi 0,
          (((ε + t : ℝ) : ℂ) ^ (-s) * Gamma s) /
            Real.sqrt (1 + t ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp [F]
      have hnum : (∫ x : ℝ in Set.Ioi 0,
          (x : ℂ) ^ (s - 1) * ↑(Real.exp (-ε * x)) *
            ↑(Real.exp (-x * t))) =
          ∫ x : ℝ in Set.Ioi 0,
            (x : ℂ) ^ (s - 1) *
              Complex.exp (-(((ε + t : ℝ) : ℂ) * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        change (x : ℂ) ^ (s - 1) * ↑(Real.exp (-ε * x)) *
            ↑(Real.exp (-x * t)) =
          (x : ℂ) ^ (s - 1) *
            Complex.exp (-(((ε + t : ℝ) : ℂ) * x))
        rw [Complex.ofReal_exp, Complex.ofReal_exp]
        have hexp : Complex.exp ((-ε * x : ℝ) : ℂ) *
            Complex.exp ((-x * t : ℝ) : ℂ) =
            Complex.exp (-(((ε + t : ℝ) : ℂ) * x)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [show (x : ℂ) ^ (s - 1) * Complex.exp ((-ε * x : ℝ) : ℂ) *
              Complex.exp ((-x * t : ℝ) : ℂ) =
            (x : ℂ) ^ (s - 1) *
              (Complex.exp ((-ε * x : ℝ) : ℂ) *
                Complex.exp ((-x * t : ℝ) : ℂ)) by ring,
          hexp]
      calc
        (∫ x : ℝ in Set.Ioi 0,
            (x : ℂ) ^ (s - 1) * ↑(Real.exp (-ε * x)) *
              (↑(Real.exp (-x * t)) / ↑(Real.sqrt (1 + t ^ 2)))) =
            (∫ x : ℝ in Set.Ioi 0,
                (x : ℂ) ^ (s - 1) * ↑(Real.exp (-ε * x)) *
                  ↑(Real.exp (-x * t))) /
              ↑(Real.sqrt (1 + t ^ 2)) := by
          rw [← MeasureTheory.integral_div]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          ring
        _ = (∫ x : ℝ in Set.Ioi 0,
              (x : ℂ) ^ (s - 1) *
                Complex.exp (-(((ε + t : ℝ) : ℂ) * x))) /
              ↑(Real.sqrt (1 + t ^ 2)) := by rw [hnum]
        _ = (((ε + t : ℝ) : ℂ) ^ (-s) * Gamma s) /
              ↑(Real.sqrt (1 + t ^ 2)) := by
          have hsumPos : 0 < ε + t := add_pos hε ht
          have hpow : (1 / (((ε + t : ℝ) : ℂ)) : ℂ) ^ s =
              (((ε + t : ℝ) : ℂ) ^ (-s)) := by
            rw [Complex.cpow_neg, one_div, Complex.inv_cpow]
            rw [Complex.arg_ofReal_of_nonneg hsumPos.le]
            exact Real.pi_ne_zero.symm
          rw [integral_cpow_mul_exp_neg_mul_Ioi_eq hs hsumPos, hpow]
    _ = (∫ t : ℝ in Set.Ioi 0,
          ((ε + t : ℝ) : ℂ) ^ (-s) /
            Real.sqrt (1 + t ^ 2)) * Gamma s := by
      rw [← MeasureTheory.integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      ring

theorem probe_integrableOn_damped_y0Osc_mellin
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
        (dfiBesselY0Osc x : ℂ)) (Set.Ioi 0) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
      Real.sin (p.1 * Real.cos p.2)
  have hjointOn : IntegrableOn F
      (Set.Ioi 0 ×ˢ Set.Ioc 0 (Real.pi / 2)) :=
    probe_integrableOn_damped_osc_joint hs hε
  have hjoint : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) := by
    simpa only [F, Measure.prod_restrict] using! hjointOn
  have hIntegrated : IntegrableOn
      (fun x : ℝ => ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2), F (x, u))
      (Set.Ioi 0) := hjoint.integral_prod_left
  refine hIntegrated.congr_fun ?_ measurableSet_Ioi
  intro x _
  change (∫ u : ℝ in Set.Ioc 0 (Real.pi / 2), F (x, u)) =
    (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
      (dfiBesselY0Osc x : ℂ)
  rw [probe_dfiBesselY0Osc_eq_integral_sin,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
    ← MeasureTheory.integral_const_mul]

theorem probe_integrableOn_damped_y0Tail_mellin
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
        (dfiBesselY0Tail x : ℂ)) (Set.Ioi 0) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * Real.exp (-ε * p.1) *
      (Real.exp (-p.1 * p.2) / Real.sqrt (1 + p.2 ^ 2))
  have hjointOn : IntegrableOn F (Set.Ioi 0 ×ˢ Set.Ioi 0) :=
    probe_integrableOn_damped_tail_joint hs hε
  have hjoint : Integrable F
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
    simpa only [F, Measure.prod_restrict] using! hjointOn
  have hIntegrated : IntegrableOn
      (fun x : ℝ => ∫ t : ℝ in Set.Ioi 0, F (x, t)) (Set.Ioi 0) :=
    hjoint.integral_prod_left
  refine hIntegrated.congr_fun ?_ measurableSet_Ioi
  intro x _
  change (∫ t : ℝ in Set.Ioi 0, F (x, t)) =
    (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
      (dfiBesselY0Tail x : ℂ)
  unfold dfiBesselY0Tail
  have htailCast :
      ↑(∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)) =
        ∫ t in Set.Ioi (0 : ℝ),
          (↑(Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)) : ℂ) := by
    exact integral_ofReal.symm
  rw [htailCast, ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp [F]
  push_cast
  ring

theorem probe_integral_cpow_mul_damped_y0_Ioi
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
          (dfiBesselY0 x : ℂ)) =
      (2 / Real.pi : ℂ) *
        (((∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
            (((ε : ℂ) - I * Real.cos u) ^ (-s) -
                ((ε : ℂ) + I * Real.cos u) ^ (-s)) / (2 * I)) * Gamma s -
          (∫ t : ℝ in Set.Ioi 0,
            ((ε + t : ℝ) : ℂ) ^ (-s) /
              Real.sqrt (1 + t ^ 2)) * Gamma s)) := by
  have hOscInt := probe_integrableOn_damped_y0Osc_mellin hs hε
  have hTailInt := probe_integrableOn_damped_y0Tail_mellin hs hε
  have hdecomp : (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
        (dfiBesselY0 x : ℂ)) =
      (2 / Real.pi : ℂ) *
        ((∫ x : ℝ in Set.Ioi 0,
            (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
              (dfiBesselY0Osc x : ℂ)) -
          (∫ x : ℝ in Set.Ioi 0,
            (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
              (dfiBesselY0Tail x : ℂ))) := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
          (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
            (dfiBesselY0 x : ℂ)) =
          ∫ x : ℝ in Set.Ioi 0, (2 / Real.pi : ℂ) *
            ((x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
                (dfiBesselY0Osc x : ℂ) -
              (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
                (dfiBesselY0Tail x : ℂ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        unfold dfiBesselY0
        push_cast
        ring
      _ = (2 / Real.pi : ℂ) *
          (∫ x : ℝ in Set.Ioi 0,
            ((x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
                (dfiBesselY0Osc x : ℂ) -
              (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
                (dfiBesselY0Tail x : ℂ))) := by
        rw [MeasureTheory.integral_const_mul]
      _ = (2 / Real.pi : ℂ) *
          ((∫ x : ℝ in Set.Ioi 0,
              (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
                (dfiBesselY0Osc x : ℂ)) -
            (∫ x : ℝ in Set.Ioi 0,
              (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) *
                (dfiBesselY0Tail x : ℂ))) := by
        rw [MeasureTheory.integral_sub hOscInt hTailInt]
  rw [hdecomp, probe_integral_cpow_mul_damped_y0Osc_Ioi hs hε,
    probe_integral_cpow_mul_damped_y0Tail_Ioi hs hε]

theorem probe_integral_cpow_mul_dfiBesselY0_Ioi_eq_beta
    {s : ℂ} (hsLower : (1 / 4 : ℝ) < s.re)
    (hsUpper : s.re < 1 / 2) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselY0 x : ℂ)) =
      (2 / Real.pi : ℂ) *
        ((((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) ((1 - s) / 2)) *
              Complex.sin (Real.pi * s / 2) * Gamma s) -
          (((1 / 2 : ℂ) * Complex.betaIntegral ((1 - s) / 2) (s / 2)) *
              Gamma s)) := by
  have hs : 0 < s.re := by linarith
  have hsOne : s.re < 1 := by linarith
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let L : ℕ → ℂ := fun n =>
    ∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (s - 1) * Real.exp (-ε n * x) *
        (dfiBesselY0 x : ℂ)
  let A : ℕ → ℂ := fun n =>
    ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
      ((((ε n : ℝ) : ℂ) - I * Real.cos u) ^ (-s) -
        (((ε n : ℝ) : ℂ) + I * Real.cos u) ^ (-s)) / (2 * I)
  let B : ℕ → ℂ := fun n =>
    ∫ t : ℝ in Set.Ioi 0,
      ((ε n + t : ℝ) : ℂ) ^ (-s) / Real.sqrt (1 + t ^ 2)
  let R : ℕ → ℂ := fun n =>
    (2 / Real.pi : ℂ) * (A n * Gamma s - B n * Gamma s)
  let linf : ℂ := ∫ x : ℝ in Set.Ioi 0,
    (x : ℂ) ^ (s - 1) * (dfiBesselY0 x : ℂ)
  let ainf : ℂ := ∫ u : ℝ in Set.Ioc 0 (Real.pi / 2),
    (Real.cos u : ℂ) ^ (-s) * Complex.sin (Real.pi * s / 2)
  let binf : ℂ := ∫ t : ℝ in Set.Ioi 0,
    (t : ℂ) ^ (-s) / Real.sqrt (1 + t ^ 2)
  let rinf : ℂ := (2 / Real.pi : ℂ) *
    (ainf * Gamma s - binf * Gamma s)
  have hL : Tendsto L atTop (𝓝 linf) := by
    simpa only [L, linf, ε] using
      probe_tendsto_damped_dfiBesselY0_mellin hsLower hsUpper
  have hA : Tendsto A atTop (𝓝 ainf) := by
    simpa only [A, ainf, ε] using probe_tendsto_damped_osc_factor hs hsOne
  have hB : Tendsto B atTop (𝓝 binf) := by
    simpa only [B, binf, ε] using probe_tendsto_damped_tail_factor hs hsOne
  have hR : Tendsto R atTop (𝓝 rinf) := by
    dsimp [R, rinf]
    exact ((hA.mul_const (Gamma s)).sub (hB.mul_const (Gamma s))).const_mul
      (2 / Real.pi : ℂ)
  have hEq : ∀ n, L n = R n := by
    intro n
    have hε : 0 < ε n := by dsimp [ε]; positivity
    simpa only [L, R, A, B] using
      (probe_integral_cpow_mul_damped_y0_Ioi hs hε)
  have hLR : linf = rinf :=
    tendsto_nhds_unique (hL.congr' (Eventually.of_forall hEq)) hR
  dsimp [linf, rinf, ainf, binf] at hLR
  rw [integral_Ioc_eq_integral_Ioo,
    MeasureTheory.integral_mul_const,
    integral_cos_cpow_neg_eq_beta,
    integral_tail_power_eq_beta] at hLR
  exact hLR

theorem probe_y0_beta_combination_eq_k0_beta
    {s : ℂ} (hs : 0 < s.re) (hsUpper : s.re < 1) :
    Complex.betaIntegral (1 / 2) ((1 - s) / 2) *
          Complex.sin (Real.pi * s / 2) -
        Complex.betaIntegral ((1 - s) / 2) (s / 2) =
      -Complex.cos (Real.pi * s / 2) *
        Complex.betaIntegral (1 / 2) (s / 2) := by
  let a : ℂ := s / 2
  let b : ℂ := (1 - s) / 2
  have ha : 0 < a.re := by
    dsimp [a]
    norm_num
    linarith
  have hb : 0 < b.re := by
    dsimp [b]
    norm_num
    linarith
  have h1ma : 0 < (1 - a).re := by
    dsimp [a]
    norm_num
    linarith
  have hah : 0 < (a + 1 / 2).re := by
    dsimp [a]
    norm_num
    linarith
  have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  have hGb : Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb
  have hG1ma : Gamma (1 - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1ma
  have hGah : Gamma (a + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hah
  have hGh : Gamma (1 / 2 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hrefA := Complex.Gamma_mul_Gamma_one_sub a
  have hrefB := Complex.Gamma_mul_Gamma_one_sub b
  have hsin : Complex.sin (Real.pi * a) ≠ 0 := by
    intro hz
    rw [hz, div_zero] at hrefA
    exact (mul_ne_zero hGa hG1ma) hrefA
  have hsinB : Complex.sin (Real.pi * b) ≠ 0 := by
    intro hz
    rw [hz, div_zero] at hrefB
    have hG1mb : Gamma (1 - b) ≠ 0 := by
      rw [show 1 - b = a + 1 / 2 by dsimp [a, b]; ring]
      exact hGah
    exact (mul_ne_zero hGb hG1mb) hrefB
  have htrigA : Real.pi * a = Real.pi * s / 2 := by
    dsimp [a]
    ring
  have htrigB : Complex.sin (Real.pi * b) =
      Complex.cos (Real.pi * s / 2) := by
    rw [show Real.pi * b = (Real.pi : ℂ) / 2 - Real.pi * s / 2 by
      dsimp [b]
      ring]
    exact Complex.sin_pi_div_two_sub _
  have hcos : Complex.cos (Real.pi * s / 2) ≠ 0 := by
    rw [← htrigB]
    exact hsinB
  have hhalf : Gamma (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Complex.Gamma_one_half_eq]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow Real.pi_pos.le]
    norm_cast
    rw [Real.sqrt_eq_rpow]
  have hhalfSq : Gamma (1 / 2 : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [hhalf]
    norm_cast
    exact Real.sq_sqrt Real.pi_pos.le
  have hrefBcos : Gamma b * Gamma (1 - b) =
      (Real.pi : ℂ) / Complex.cos (Real.pi * s / 2) := by
    rw [hrefB, htrigB]
  have hfirst :
      Gamma (1 / 2 : ℂ) * Gamma b / Gamma (1 - a) *
          Complex.sin (Real.pi * a) =
        Gamma a * Gamma b / Gamma (1 / 2 : ℂ) *
          Complex.sin (Real.pi * a) ^ 2 := by
    have hrefAcleared : Gamma a * Gamma (1 - a) *
        Complex.sin (Real.pi * a) = (Real.pi : ℂ) := by
      calc
        Gamma a * Gamma (1 - a) * Complex.sin (Real.pi * a) =
            ((Real.pi : ℂ) / Complex.sin (Real.pi * a)) *
              Complex.sin (Real.pi * a) := by rw [hrefA]
        _ = (Real.pi : ℂ) := div_mul_cancel₀ _ hsin
    field_simp [hG1ma, hGh, hsin]
    rw [hhalfSq]
    nth_rewrite 1 [← hrefAcleared]
    ring_nf
  have hthird :
      Complex.cos (Real.pi * a) *
          (Gamma (1 / 2 : ℂ) * Gamma a / Gamma (a + 1 / 2)) =
        Gamma a * Gamma b / Gamma (1 / 2 : ℂ) *
          Complex.cos (Real.pi * a) ^ 2 := by
    have hcosA : Complex.cos (Real.pi * a) ≠ 0 := by
      rw [htrigA]
      exact hcos
    have hrefBcosA : Gamma b * Gamma (a + 1 / 2) =
        (Real.pi : ℂ) / Complex.cos (Real.pi * a) := by
      rw [show a + 1 / 2 = 1 - b by dsimp [a, b]; ring, hrefB]
      have htrigBA : Complex.sin (Real.pi * b) =
          Complex.cos (Real.pi * a) := by
        calc
          Complex.sin (Real.pi * b) = Complex.cos (Real.pi * s / 2) := htrigB
          _ = Complex.cos (Real.pi * a) := by rw [htrigA]
      rw [htrigBA]
    field_simp [hGah, hGh, hcosA]
    rw [show (a * 2 + 1) / 2 = a + 1 / 2 by ring, hhalfSq]
    have hrefBcleared : Gamma b * Gamma (a + 1 / 2) *
        Complex.cos (Real.pi * a) = (Real.pi : ℂ) := by
      calc
        Gamma b * Gamma (a + 1 / 2) * Complex.cos (Real.pi * a) =
            ((Real.pi : ℂ) / Complex.cos (Real.pi * a)) *
              Complex.cos (Real.pi * a) := by rw [hrefBcosA]
        _ = (Real.pi : ℂ) := div_mul_cancel₀ _ hcosA
    apply (div_eq_iff hGah).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hrefBcleared.symm
  rw [show (1 - s) / 2 = b by rfl, show s / 2 = a by rfl]
  rw [Complex.betaIntegral_eq_Gamma_mul_div (1 / 2) b (by norm_num) hb,
    Complex.betaIntegral_eq_Gamma_mul_div b a hb ha,
    Complex.betaIntegral_eq_Gamma_mul_div (1 / 2) a (by norm_num) ha]
  rw [show (1 / 2 : ℂ) + b = 1 - a by dsimp [a, b]; ring,
    show b + a = (1 / 2 : ℂ) by dsimp [a, b]; ring,
    show (1 / 2 : ℂ) + a = a + 1 / 2 by ring,
    ← htrigA]
  rw [hfirst]
  rw [neg_mul, hthird]
  rw [show Gamma b * Gamma a / Gamma (1 / 2 : ℂ) =
      Gamma a * Gamma b / Gamma (1 / 2 : ℂ) by ring]
  have htrig := Complex.sin_sq_add_cos_sq (Real.pi * a)
  have hsinMinus : Complex.sin (Real.pi * a) ^ 2 - 1 =
      -Complex.cos (Real.pi * a) ^ 2 := by
    nth_rewrite 1 [← htrig]
    ring
  calc
    Gamma a * Gamma b / Gamma (1 / 2 : ℂ) *
          Complex.sin (Real.pi * a) ^ 2 -
        Gamma a * Gamma b / Gamma (1 / 2 : ℂ) =
      Gamma a * Gamma b / Gamma (1 / 2 : ℂ) *
        (Complex.sin (Real.pi * a) ^ 2 - 1) := by ring
    _ = Gamma a * Gamma b / Gamma (1 / 2 : ℂ) *
        (-Complex.cos (Real.pi * a) ^ 2) := by rw [hsinMinus]
    _ = -(Gamma a * Gamma b / Gamma (1 / 2 : ℂ) *
        Complex.cos (Real.pi * a) ^ 2) := by ring

theorem probe_integral_cpow_mul_dfiBesselY0_Ioi_eq
    {s : ℂ} (hsLower : (1 / 4 : ℝ) < s.re)
    (hsUpper : s.re < 1 / 2) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (dfiBesselY0 x : ℂ)) =
      dfiBesselY0MellinSymbol s := by
  rw [probe_integral_cpow_mul_dfiBesselY0_Ioi_eq_beta hsLower hsUpper]
  have hs : 0 < s.re := by linarith
  have hsOne : s.re < 1 := by linarith
  have hbeta := probe_y0_beta_combination_eq_k0_beta hs hsOne
  have hk := half_beta_mul_Gamma_eq_besselK0MellinSymbol hs
  have hbridge : dfiBesselY0MellinSymbol s =
      -(2 / Real.pi : ℂ) * Complex.cos (Real.pi * s / 2) *
        dfiBesselK0MellinSymbol s := by
    unfold dfiBesselY0MellinSymbol dfiBesselK0MellinSymbol
    have h2 : (2 : ℂ) ^ (s - 1) =
        2 * (2 : ℂ) ^ (s - 2) := by
      calc
        (2 : ℂ) ^ (s - 1) =
            (2 : ℂ) ^ ((1 : ℂ) + (s - 2)) := by congr 1; ring
        _ = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (s - 2) := by
          rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
        _ = 2 * (2 : ℂ) ^ (s - 2) := by simp
    rw [h2]
    ring
  calc
    (2 / Real.pi : ℂ) *
          ((((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) ((1 - s) / 2)) *
                Complex.sin (Real.pi * s / 2) * Gamma s) -
            (((1 / 2 : ℂ) * Complex.betaIntegral ((1 - s) / 2) (s / 2)) *
                Gamma s)) =
        (2 / Real.pi : ℂ) *
          ((1 / 2 : ℂ) *
            (Complex.betaIntegral (1 / 2) ((1 - s) / 2) *
                Complex.sin (Real.pi * s / 2) -
              Complex.betaIntegral ((1 - s) / 2) (s / 2)) * Gamma s) := by
            ring
    _ = -(2 / Real.pi : ℂ) * Complex.cos (Real.pi * s / 2) *
          (((1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s / 2)) *
            Gamma s) := by rw [hbeta]; ring
    _ = -(2 / Real.pi : ℂ) * Complex.cos (Real.pi * s / 2) *
          dfiBesselK0MellinSymbol s := by rw [hk]
    _ = dfiBesselY0MellinSymbol s := hbridge.symm

/-- Absolute Mellin convergence of the square-root-scaled Neumann kernel on
the source strip used for the physical DFI equation-(29) transform. -/
theorem mellinConvergent_dfiBesselY0_mul_sqrt
    {A : ℝ} (hA : 0 < A) {s : ℂ}
    (hsLower : (1 / 8 : ℝ) < s.re)
    (hsUpper : s.re < 1 / 4) :
    MellinConvergent
      (fun x : ℝ => (dfiBesselY0 (A * Real.sqrt x) : ℂ)) s := by
  have hbase : MellinConvergent
      (fun y : ℝ => (dfiBesselY0 y : ℂ)) (2 * s) := by
    apply probe_mellinConvergent_dfiBesselY0
    · norm_num
      linarith
    · norm_num
      linarith
  have hscaled : MellinConvergent
      (fun y : ℝ => (dfiBesselY0 (A * y) : ℂ)) (2 * s) :=
    (MellinConvergent.comp_mul_left hA).2 hbase
  have hscaled' : MellinConvergent
      (fun y : ℝ => (dfiBesselY0 (A * y) : ℂ))
        (s / ((1 / 2 : ℝ) : ℂ)) := by
    convert hscaled using 1
    norm_num
    ring
  have hroot := (MellinConvergent.comp_rpow
    (f := fun y : ℝ => (dfiBesselY0 (A * y) : ℂ))
    (s := s) (a := (1 / 2 : ℝ)) (by norm_num)).2 hscaled'
  simpa only [Real.sqrt_eq_rpow] using hroot

/-- Exact Mellin transform of the square-root-scaled Neumann kernel on its
absolute strip.  This is the literal physical transform needed to replace
the analytically continued symbol in DFI equation (29). -/
theorem mellin_dfiBesselY0_mul_sqrt
    {A : ℝ} (hA : 0 < A) {s : ℂ}
    (hsLower : (1 / 8 : ℝ) < s.re)
    (hsUpper : s.re < 1 / 4) :
    mellin (fun x : ℝ => (dfiBesselY0 (A * Real.sqrt x) : ℂ)) s =
      2 * (A : ℂ) ^ (-(2 * s)) * dfiBesselY0MellinSymbol (2 * s) := by
  have hroot : (fun x : ℝ => (dfiBesselY0 (A * Real.sqrt x) : ℂ)) =
      (fun x : ℝ => (dfiBesselY0 (A * x ^ (1 / 2 : ℝ)) : ℂ)) := by
    funext x
    rw [Real.sqrt_eq_rpow]
  rw [hroot]
  change mellin
    (fun x : ℝ => (dfiBesselY0 (A * (x ^ (1 / 2 : ℝ))) : ℂ)) s = _
  rw [mellin_comp_rpow
    (fun y : ℝ => (dfiBesselY0 (A * y) : ℂ)) s (1 / 2 : ℝ)]
  norm_num
  norm_num [div_eq_mul_inv] at ⊢
  have hmul : s * 2 = 2 * s := by ring
  rw [hmul]
  have hscale := mellin_comp_mul_left
    (fun y : ℝ => (dfiBesselY0 y : ℂ)) (2 * s) hA
  change 2 * mellin (fun y : ℝ => (dfiBesselY0 (A * y) : ℂ)) (2 * s) = _
  rw [hscale]
  have hs2Lower : (1 / 4 : ℝ) < (2 * s).re := by
    norm_num
    linarith
  have hs2Upper : (2 * s).re < (1 / 2 : ℝ) := by
    norm_num
    linarith
  have hy : mellin (fun y : ℝ => (dfiBesselY0 y : ℂ)) (2 * s) =
      dfiBesselY0MellinSymbol (2 * s) := by
    unfold mellin
    simpa only [smul_eq_mul] using
      probe_integral_cpow_mul_dfiBesselY0_Ioi_eq hs2Lower hs2Upper
  rw [hy]
  ring

end MathCollab.Density.Stronger.Atkinson
