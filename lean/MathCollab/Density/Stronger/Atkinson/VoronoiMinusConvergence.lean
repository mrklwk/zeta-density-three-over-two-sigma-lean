module
-- Reversible module-visibility port of the audited development.
/-
Native convergence for the literal DFI minus Mellin integrand. Selected
contour target: McColm DFIEquation29.lean at
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1 (2026, MIT-0).
All test-function Mellin decay and multiplier bounds are proved imports.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiMultiplierBounds
public import MathCollab.Density.Stronger.Atkinson.VoronoiMellinDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory Filter Topology
open MathCollab.Density.Contour
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def dfiVoronoiMinusIntegrand (q : ℕ) [NeZero q] (g : ℝ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (n:ℂ)^(-(1-z))*dfiVoronoiMinusMultiplier q z*mellin g z

theorem differentiableAt_dfiVoronoiMinusIntegrand (q : ℕ) [NeZero q]
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {n : ℕ} (hn : 0<n)
    {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiVoronoiMinusIntegrand q g n) z := by
  have hc : DifferentiableAt ℂ (fun w : ℂ => (n:ℂ)^(-(1-w))) z :=
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -(1-w)) z).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))
  exact (hc.mul (differentiableAt_dfiVoronoiMinusMultiplier_of_re_lt_one q hz)).mul
    (hg.differentiable_mellin z)

theorem norm_voronoiNatPower_le_one {n : ℕ} (hn : 0<n) {z : ℂ} (hz : z.re ≤ 1) :
    ‖(n:ℂ)^(-(1-z))‖ ≤ 1 := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast hn
  · simp only [neg_re, sub_re, one_re]; linarith

theorem DFIVoronoiTestFunction.exists_minusIntegrand_strip_decay (q : ℕ) [NeZero q]
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0<n → ∀ σ : ℝ,
      -(1/2 : ℝ) ≤ σ → σ ≤ 13/16 → ∀ u : ℝ,
      ‖dfiVoronoiMinusIntegrand q g n ((σ:ℂ)+(u:ℂ)*I)‖ ≤ C/(1+|u|)^2 := by
  obtain ⟨D,hD,hm⟩ := hg.exists_mellin_weighted_strip_bound 4
  refine ⟨10368*(q:ℝ)^3*D, by positivity, ?_⟩
  intro n hn σ hlo hhi u
  let z : ℂ := (σ:ℂ)+(u:ℂ)*I
  have hzre : z.re = σ := by simp [z]
  have hzim : z.im = u := by simp [z]
  have hp := norm_voronoiNatPower_le_one hn (z := z) (by rw [hzre]; linarith)
  have hmul := norm_dfiVoronoiMinusMultiplier_strip_le q
    (z := z) (by simpa only [hzre]) (by simpa only [hzre])
  rw [hzim] at hmul
  have hm' := hm σ hlo (by linarith) u
  apply (le_div_iff₀ (by positivity : 0 < (1+|u|)^2)).mpr
  change ‖dfiVoronoiMinusIntegrand q g n z‖*(1+|u|)^2 ≤ _
  unfold dfiVoronoiMinusIntegrand
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (1*(10368*(q:ℝ)^3*(1+|u|)^2))*‖mellin g z‖*(1+|u|)^2 := by gcongr
    _ = (10368*(q:ℝ)^3)*((1+|u|)^4*‖mellin g z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm' (by positivity)

theorem DFIVoronoiTestFunction.continuous_minusIntegrand_vertical (q : ℕ) [NeZero q]
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {n : ℕ} (hn : 0<n)
    {σ : ℝ} (hσ : σ < 1) :
    Continuous (fun u : ℝ => dfiVoronoiMinusIntegrand q g n ((σ:ℂ)+(u:ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hc := (differentiableAt_dfiVoronoiMinusIntegrand q hg hn
    (z := (σ:ℂ)+(u:ℂ)*I) (by simpa using hσ)).continuousAt
  exact hc.comp (f := fun v : ℝ => (σ:ℂ)+(v:ℂ)*I) (by fun_prop)

theorem DFIVoronoiTestFunction.integrable_minusIntegrand_vertical (q : ℕ) [NeZero q]
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {n : ℕ} (hn : 0<n)
    {σ : ℝ} (hσ : -(1/2 : ℝ) ≤ σ) (hσ' : σ ≤ 13/16) :
    Integrable (fun u : ℝ => dfiVoronoiMinusIntegrand q g n ((σ:ℂ)+(u:ℂ)*I)) := by
  obtain ⟨C,hC,hb⟩ := hg.exists_minusIntegrand_strip_decay q
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    (hg.continuous_minusIntegrand_vertical q hn (by linarith)).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro u
  calc
    _ ≤ C/(1+|u|)^2 := hb n hn σ hσ hσ' u
    _ ≤ C/(1+u^2) := div_le_div_of_nonneg_left hC (by positivity)
      (by nlinarith [sq_abs u, abs_nonneg u])
    _ = _ := by rw [div_eq_mul_inv]

theorem DFIVoronoiTestFunction.minusIntegrand_horizontal_limits (q : ℕ) [NeZero q]
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {n : ℕ} (hn : 0<n) :
    Tendsto (fun H : ℝ => HIntegral' (dfiVoronoiMinusIntegrand q g n) (-(1/2)) (13/16) H)
        atTop (𝓝 0) ∧
      Tendsto (fun H : ℝ => HIntegral' (dfiVoronoiMinusIntegrand q g n) (-(1/2)) (13/16) (-H))
        atTop (𝓝 0) := by
  obtain ⟨C,hC,hdecay⟩ := hg.exists_minusIntegrand_strip_decay q
  have hbound (H : ℝ) :
      ‖HIntegral (dfiVoronoiMinusIntegrand q g n) (-(1/2)) (13/16) H‖ ≤
        C/(1+|H|)^2*(21/16) := by
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(1/2 : ℝ)) (b := (13/16 : ℝ))
      (f := fun x : ℝ => dfiVoronoiMinusIntegrand q g n ((x:ℂ)+(H:ℂ)*I))
      (C := C/(1+|H|)^2) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : -(1/2 : ℝ) ≤ 13/16)] at hx'
        exact hdecay n hn x hx'.1 hx'.2 H)
    convert hInt using 1 <;> norm_num [HIntegral]
  have hEnv : Tendsto (fun H : ℝ => C/(1+|H|)^2*(21/16)) atTop (𝓝 0) := by
    have ha : Tendsto (fun H : ℝ => |H|) atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall fun H => le_abs_self H) tendsto_id
    have hd : Tendsto (fun H : ℝ => (1+|H|)^2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp (tendsto_const_nhds.add_atTop ha)
    have h := (tendsto_const_nhds (x := C)).div_atTop hd
    simpa using h.mul_const (21/16)
  have htop : Tendsto (fun H : ℝ => HIntegral (dfiVoronoiMinusIntegrand q g n) (-(1/2)) (13/16) H)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hbound hEnv
  have hbottom : Tendsto (fun H : ℝ => HIntegral (dfiVoronoiMinusIntegrand q g n) (-(1/2)) (13/16) (-H))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ hEnv
    intro H
    simpa only [abs_neg] using hbound (-H)
  constructor
  · simpa [HIntegral'] using htop.const_smul (1/(2*Real.pi*I) : ℂ)
  · simpa [HIntegral'] using hbottom.const_smul (1/(2*Real.pi*I) : ℂ)

end MathCollab.Density.Stronger.Atkinson
