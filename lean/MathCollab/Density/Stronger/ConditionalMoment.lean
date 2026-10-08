module
-- Reversible module-visibility port of the audited development.
/- Selected high/low moment calculus adapted from Scott McColm, MIT-0,
exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
The actual fourth-moment and high-value-tail inputs remain explicit parameters.
See ../../../../third_party/twelfth/HIGH_LOW_MOMENT_MANIFEST.json and LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.MomentGrowth
public import MathCollab.Density.Stronger.DyadicMoment
public import WeylPort.GrowthAlgebra

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open MeasureTheory Filter Set
open scoped Interval
open TaoTrudgianYang2025 (eventually_const_height_log_pow_mul_rpow_le_rpow)
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem log_height_cube_div_le {H A : ℝ} (hH : 1 ≤ H) (hA : 1 ≤ A) :
    Real.log (H^3/A) ≤ 3*Real.log H := by
  have hH0 : 0 < H := by linarith
  have hA0 : 0 < A := by linarith
  rw [Real.log_div (by positivity : H^3 ≠ 0) hA0.ne',Real.log_pow]
  have hlog := Real.log_nonneg hA
  norm_num
  linarith

theorem eventually_zeta_high_log_budget {η ε : ℝ} (hgap : η < ε) :
    ∀ᶠ H : ℝ in atTop,
      2*H^(2+η)*(1+3*Real.log H) ≤ H^(2+ε) := by
  have h0 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 4) (a := 2+η) (b := 2+ε) (by norm_num) 0 (by linarith)
  have h1 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 12) (a := 2+η) (b := 2+ε) (by norm_num) 1 (by linarith)
  filter_upwards [h0,h1,eventually_ge_atTop (1:ℝ)] with H h0 h1 hH
  simp only [pow_zero,mul_one,pow_one] at h0 h1
  have hlog : Real.log H ≤ Real.log (3*H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ H^(2+η))
  nlinarith

/-- High twelfth moment from the literal high-value measure bound, with
all growth and integrability supplied by proved actual-zeta lemmas. -/
theorem zeta_twelfth_high_eventually_of_tail
    (hTail : ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+η)/V^12))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop,
      (∫ t in pointValueSuperlevel H (H^(1/8+ε)), zetaMomentCriticalNorm t^12) ≤ H^(2+ε) := by
  let η : ℝ := min (ε/2) (1/100)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/100 := min_le_right _ _
  have hηε : η < ε := (min_le_left _ _).trans_lt (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ),hTail η hη,
    zetaMomentCriticalNorm_twelfth_eventually_le_cube,eventually_zeta_high_log_budget hηε]
    with H hH1 hcount hGrowth hbudget
  have hH0 : 0 < H := by linarith
  let V : ℝ := H^(1/8+η)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hV1 : 1 ≤ V := Real.one_le_rpow hH1 (by linarith)
  have hA1 : 1 ≤ V^12 := one_le_pow₀ hV1
  have hVM : V^12 ≤ H^3 := by
    dsimp only [V]
    rw [← Real.rpow_mul_natCast hH0.le]
    calc
      H^((1/8+η)*(12:ℝ)) ≤ H^(3:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = H^3 := Real.rpow_natCast H 3
  have hvol : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal ((2*H^(2+η))/U^12) := by
    intro U hVU
    exact hcount U (hV.trans_le hVU) hVU
  have hi := zeta_twelfth_high_integral_le_log hV hVM
    (by positivity : 0 ≤ 2*H^(2+η))
    (fun t ht => hGrowth t ⟨ht.1,ht.2.1⟩) hvol
  have hlog := log_height_cube_div_le hH1 hA1
  have hsubset : pointValueSuperlevel H (H^(1/8+ε)) ⊆ pointValueSuperlevel H V := by
    intro t ht
    refine ⟨ht.1,ht.2.1,?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans ht.2.2
  calc
    _ ≤ ∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12 :=
      setIntegral_mono_set (integrableOn_zeta_twelfth_pointValueSuperlevel H V)
        (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall hsubset)
    _ ≤ (2*H^(2+η))*(1+Real.log (H^3/V^12)) := hi
    _ ≤ 2*H^(2+η)*(1+3*Real.log H) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ H^(2+ε) := hbudget

/-- Complete high/low assembly with both genuine analytic producers explicit.
The statement does not supply either the fourth moment or the high-value tail. -/
theorem zeta_twelfth_dyadic_of_fourth_and_tail
    (hFourth : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η))
    (hTail : ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+η)/V^12)) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε) := by
  intro ε hε
  let η : ℝ := ε/20
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨C,hC,hfourth⟩ := hFourth η hη
  refine ⟨1+C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),hfourth,zeta_twelfth_high_eventually_of_tail hTail hη]
    with H hH1 hfourthH hhigh
  have hH0 : 0 < H := by linarith
  have hsplit := zeta_twelfth_integral_le_high_add_fourth (V := H^(1/8+η)) hH0.le
  have hv : (H^(1/8+η))^8*H^(1+η) = H^(2+9*η) := by
    rw [← Real.rpow_mul_natCast hH0.le,← Real.rpow_add hH0]
    congr 1
    norm_num
    ring
  have he1 : 2+η ≤ 2+ε := by dsimp only [η]; linarith
  have he9 : 2+9*η ≤ 2+ε := by dsimp only [η]; linarith
  calc
    _ ≤ (∫ t in pointValueSuperlevel H (H^(1/8+η)), zetaMomentCriticalNorm t^12) +
          (H^(1/8+η))^8*(∫ t in H..2*H, zetaMomentCriticalNorm t^4) := hsplit
    _ ≤ H^(2+η)+(H^(1/8+η))^8*(C*H^(1+η)) :=
      add_le_add hhigh (mul_le_mul_of_nonneg_left hfourthH (by positivity))
    _ = H^(2+η)+C*H^(2+9*η) := by rw [mul_left_comm _ C,hv]
    _ ≤ H^(2+ε)+C*H^(2+ε) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hH1 he1)
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 he9) hC)
    _ = (1+C)*H^(2+ε) := by ring

/-- Dyadic actual-zeta bounds imply the literal physical moment used by the
conditional density theorem. No extra exponent is spent. -/
theorem zeta_twelfth_physical_of_dyadic {ε D : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hdyad : ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε) := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp hdyad
  obtain ⟨K,hK,hfull⟩ := integral_zero_le_of_dyadic
    (fun t => zetaMomentCriticalNorm t^12) (continuous_zetaMomentCriticalNorm.pow 12)
    (fun _ => by positivity) (show 1 ≤ 2+ε by linarith)
    (le_max_left 1 B) hD (fun H hH => hB H ((le_max_right _ _).trans hH))
  refine ⟨K*(3:ℝ)^(2+ε),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 B)] with T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTp : 0 < T := by linarith
  have hh := hfull (3*T) (by linarith)
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 3*T),
    ← integral_Icc_eq_integral_Ioc] at hh
  apply hh.trans_eq
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hTp.le]
  ring

/-- The complete actual-moment consumer, with exactly the fourth-moment and
high-value-measure producers left as explicit hypotheses. -/
theorem zeta_twelfth_physical_of_fourth_and_tail
    (hFourth : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η))
    (hTail : ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+η)/V^12)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε) := by
  intro ε hε
  obtain ⟨D,hD,hd⟩ := zeta_twelfth_dyadic_of_fourth_and_tail hFourth hTail ε hε
  exact zeta_twelfth_physical_of_dyadic hε hD.le hd

end MathCollab.Density.Stronger
