module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.DampedCutoff
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
Uniform Mellin estimates for smooth exponentially damped cutoffs supported
in a fixed positive compact interval. Constants precede the damping parameter
and the real part in a fixed vertical strip.
-/

open Real Set MeasureTheory
open scoped BigOperators ContDiff FourierTransform
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Composition with a fixed smooth map preserves uniform derivative bounds
on a compact set. The bound is uniform in the whole outer family. -/
theorem uniform_derivatives_comp_on_compact {ι : Type*} {f : ι → ℝ → ℝ}
    {g : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (hg : ContDiff ℝ ∞ g)
    (hbound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p x, ‖iteratedDeriv n (f p) x‖ ≤ C)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p x, x ∈ K → ‖iteratedDeriv n (f p ∘ g) x‖ ≤ C := by
  choose B hBpos hB using hbound
  have hb (i : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ‖iteratedDeriv i g x‖ ≤ D := by
    obtain ⟨D, hD⟩ := hK.bddAbove_image
      ((hg.continuous_iteratedDeriv i (by simp)).norm.continuousOn)
    exact ⟨max D 0, le_max_right _ _, fun x hx =>
      (hD ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  choose D hDpos hD using hb
  refine ⟨∑ c : OrderedFinpartition n, B c.length * ∏ j, D (c.partSize j), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hBpos _) (Finset.prod_nonneg (fun j _ => hDpos _)))
  · intro p x hx
    rw [iteratedDeriv_comp_eq_sum_orderedFinpartition (hf p).contDiffAt hg.contDiffAt
      (show (n : ℕ∞ω) ≤ ∞ by simp)]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hB _ p _) (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun j _ => hD _ x hx)) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (hBpos _)

theorem uniform_derivatives_mul_on_compact {ι κ : Type*} {f : ι → ℝ → ℝ}
    {g : κ → ℝ → ℝ} {K : Set ℝ}
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (hg : ∀ q, ContDiff ℝ ∞ (g q))
    (hboundf : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p x, x ∈ K → ‖iteratedDeriv n (f p) x‖ ≤ C)
    (hboundg : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q x, x ∈ K → ‖iteratedDeriv n (g q) x‖ ≤ C)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q x, x ∈ K →
      ‖iteratedDeriv n (fun y => f p y * g q y) x‖ ≤ C := by
  choose B hBpos hB using hboundf
  choose D hDpos hD using hboundg
  refine ⟨∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * B i * D (n-i), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hBpos _)) (hDpos _))
  · intro p q x hx
    rw [iteratedDeriv_fun_mul ((hf p).of_le (by simp)).contDiffAt
      ((hg q).of_le (by simp)).contDiffAt]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB _ p x hx) (Nat.cast_nonneg _))
      (hD _ q x hx) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hBpos _))

/-- The real logarithmic lift whose Fourier transform is the Mellin transform
on the line of real part σ. -/
def dampedMellinLift (ψ : ℝ → ℝ) (σ q u : ℝ) : ℝ :=
  Real.exp (-σ*u) * dampedCutoff ψ q (Real.exp (-u))

theorem dampedMellinLift_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (σ q : ℝ) :
    ContDiff ℝ ∞ (dampedMellinLift ψ σ q) := by
  exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
    ((dampedCutoff_contDiff hψ q).comp (Real.contDiff_exp.comp contDiff_neg))

theorem dampedMellinLift_tsupport {ψ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b) (σ q : ℝ) :
    tsupport (dampedMellinLift ψ σ q) ⊆ Icc (-Real.log b) (-Real.log a) := by
  apply closure_minimal ?_ isClosed_Icc
  intro u hu
  by_contra hn
  have hexp : Real.exp (-u) ∉ Icc a b := by
    intro hx
    apply hn
    constructor
    · have h := Real.exp_le_exp.mp
        (show Real.exp (-u) ≤ Real.exp (Real.log b) by simpa [Real.exp_log hb] using hx.2)
      linarith
    · have h := Real.exp_le_exp.mp
        (show Real.exp (Real.log a) ≤ Real.exp (-u) by simpa [Real.exp_log ha] using hx.1)
      linarith
  have hz : ψ (Real.exp (-u)) = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => hexp (hs hh))
  exact hu (by simp [dampedMellinLift, dampedCutoff, hz])

/-- A single bound before both σ in a fixed strip and q≥0. -/
theorem dampedMellinLift_uniform_derivatives {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (s₀ s₁ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc s₀ s₁, ∀ q : ℝ, 0 ≤ q → ∀ u : ℝ,
      ‖iteratedDeriv n (dampedMellinLift ψ σ q) u‖ ≤ C := by
  let K := Icc (-Real.log b) (-Real.log a)
  have hw (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ : {σ : ℝ // σ ∈ Icc s₀ s₁}, ∀ u ∈ K,
        ‖iteratedDeriv i (fun x : ℝ => Real.exp (-σ.val*x)) u‖ ≤ C := by
    have hc : Continuous (fun p : ℝ × ℝ => ‖(-p.1)^i * Real.exp (-p.1*p.2)‖) := by fun_prop
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc : IsCompact K)).bddAbove_image hc.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro σ u hu
    rw [iteratedDeriv_exp_const_mul]
    exact (hC ⟨(σ.val,u), ⟨σ.property, hu⟩, rfl⟩).trans (le_max_left _ _)
  have hf (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : {q : ℝ // 0 ≤ q}, ∀ x : ℝ, ‖iteratedDeriv i (dampedCutoff ψ q.val) x‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := dampedCutoff_uniform_derivatives hψ ha hs i
    exact ⟨C,hC,fun q x => h q.val q.property x⟩
  have hg : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) := Real.contDiff_exp.comp contDiff_neg
  have hcomp := uniform_derivatives_comp_on_compact (f := fun q : {q : ℝ // 0 ≤ q} =>
      dampedCutoff ψ q.val) (g := fun u : ℝ => Real.exp (-u))
      (isCompact_Icc : IsCompact K) (fun q => dampedCutoff_contDiff hψ q.val) hg hf
  obtain ⟨C,hC,h⟩ := uniform_derivatives_mul_on_compact
    (f := fun σ : {σ : ℝ // σ ∈ Icc s₀ s₁} => fun u : ℝ => Real.exp (-σ.val*u))
    (g := fun q : {q : ℝ // 0 ≤ q} => dampedCutoff ψ q.val ∘ (fun u : ℝ => Real.exp (-u)))
    (fun σ => by fun_prop) (fun q => (dampedCutoff_contDiff hψ q.val).comp hg) hw hcomp n
  refine ⟨C,hC,?_⟩
  intro σ hσ q hq u
  by_cases hu : u ∈ K
  · exact h ⟨σ,hσ⟩ ⟨q,hq⟩ u hu
  · have hn : u ∉ tsupport (iteratedDeriv n (dampedMellinLift ψ σ q)) := by
      intro hh
      exact hu (dampedMellinLift_tsupport ha hb hs σ q
        (tsupport_iteratedDeriv_subset _ n hh))
    rw [image_eq_zero_of_notMem_tsupport hn, norm_zero]
    exact hC

theorem tsupport_iteratedDeriv_complex_subset (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]; exact Subset.rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- Uniform compact support and uniform derivatives give uniform Fourier decay. -/
theorem uniform_fourier_power_bound {ι : Type*} {f : ι → ℝ → ℂ}
    {a b : ℝ} (hf : ∀ p, ContDiff ℝ ∞ (f p))
    (hs : ∀ p, tsupport (f p) ⊆ Icc a b)
    (hbound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p x, ‖iteratedDeriv n (f p) x‖ ≤ C)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ξ, |ξ|^n * ‖𝓕 (f p) ξ‖ ≤ C := by
  obtain ⟨B,hB,h⟩ := hbound n
  refine ⟨B * volume.real (Icc a b) / (2*Real.pi)^n, by positivity, ?_⟩
  intro p ξ
  have hs' (i : ℕ) : tsupport (iteratedDeriv i (f p)) ⊆ Icc a b :=
    (tsupport_iteratedDeriv_complex_subset _ _).trans (hs p)
  have hint (i : ℕ) (_ : (i : ℕ∞) ≤ ⊤) : Integrable (iteratedDeriv i (f p)) :=
    ((hf p).continuous_iteratedDeriv i (by simp)).integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs' i))
  have hF : ‖𝓕 (iteratedDeriv n (f p)) ξ‖ ≤ B * volume.real (Icc a b) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b) (fun x hx => by
      have hz : iteratedDeriv n (f p) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => hx (hs' n hh))
      rw [hz, smul_zero])]
    apply norm_setIntegral_le_of_norm_le_const_ae' (isCompact_Icc.measure_lt_top)
    exact Filter.Eventually.of_forall (fun x _ => by
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact h p x)
  rw [Real.fourier_iteratedDeriv (N := ⊤) (hf p) hint (by simp), norm_smul,
    norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_real, Real.norm_eq_abs] at hF
  norm_num at hF
  apply (le_div_iff₀ (pow_pos (by positivity : (0:ℝ) < 2*Real.pi) n)).2
  simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hF

theorem norm_iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (fun x => (f x : ℂ)) u‖ = ‖iteratedDeriv n f u‖ := by
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Complex.ofRealLI_apply, Function.comp_def] using
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := u) hf.contDiffAt (i := n) (by simp)

/-- Exact Mellin--Fourier conversion on every real vertical line. -/
theorem dampedCutoff_mellin_eq_fourier (ψ : ℝ → ℝ) (σ q r : ℝ) :
    mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ) + r*Complex.I) =
      𝓕 (fun u => (dampedMellinLift ψ σ q u : ℂ)) (r/(2*Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun : (fun u : ℝ => Real.exp (-((σ : ℂ) + r*Complex.I).re*u) •
      (dampedCutoff ψ q (Real.exp (-u)) : ℂ)) =
      (fun u => (dampedMellinLift ψ σ q u : ℂ)) := by
    funext u
    simp [dampedMellinLift, Complex.real_smul]
  rw [hfun]
  simp

theorem dampedCutoff_uniform_mellin_power_bound {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (s₀ s₁ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc s₀ s₁, ∀ q : ℝ, 0 ≤ q → ∀ r : ℝ,
      |r|^n * ‖mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ) + r*Complex.I)‖ ≤ C := by
  let P := {σ : ℝ // σ ∈ Icc s₀ s₁} × {q : ℝ // 0 ≤ q}
  let f : P → ℝ → ℂ := fun p u => (dampedMellinLift ψ p.1.val p.2.val u : ℂ)
  have hfc (p : P) : ContDiff ℝ ∞ (f p) :=
    Complex.ofRealCLM.contDiff.comp (dampedMellinLift_contDiff hψ _ _)
  have hfs (p : P) : tsupport (f p) ⊆ Icc (-Real.log b) (-Real.log a) :=
    (tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) rfl _).trans
      (dampedMellinLift_tsupport ha hb hs _ _)
  have hfb (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p u, ‖iteratedDeriv i (f p) u‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := dampedMellinLift_uniform_derivatives hψ ha hb hs s₀ s₁ i
    refine ⟨C,hC,?_⟩
    intro p u
    rw [norm_iteratedDeriv_ofReal (dampedMellinLift_contDiff hψ _ _)]
    exact h p.1.val p.1.property p.2.val p.2.property u
  obtain ⟨B,hB,h⟩ := uniform_fourier_power_bound hfc hfs hfb n
  refine ⟨B*(2*Real.pi)^n, by positivity, ?_⟩
  intro σ hσ q hq r
  rw [dampedCutoff_mellin_eq_fourier]
  have hp := h (⟨σ,hσ⟩,⟨q,hq⟩) (r/(2*Real.pi))
  have hp' : (|r|^n * ‖𝓕 (fun u => (dampedMellinLift ψ σ q u : ℂ))
      (r/(2*Real.pi))‖) / (2*Real.pi)^n ≤ B := by
    simpa only [f, abs_div, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi), div_pow,
      div_mul_eq_mul_div] using hp
  exact (div_le_iff₀ (pow_pos (by positivity) n)).mp hp'

/-- Literal arbitrary-order decay with a constant uniform in q≥0 and the strip. -/
theorem dampedCutoff_uniform_mellin_decay {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (s₀ s₁ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc s₀ s₁, ∀ q : ℝ, 0 ≤ q → ∀ r : ℝ,
      ‖mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ) + r*Complex.I)‖ ≤
        C / (1+|r|)^n := by
  obtain ⟨B₀,hB₀,h₀⟩ := dampedCutoff_uniform_mellin_power_bound hψ ha hb hs s₀ s₁ 0
  obtain ⟨Bₙ,hBₙ,hₙ⟩ := dampedCutoff_uniform_mellin_power_bound hψ ha hb hs s₀ s₁ n
  refine ⟨2^n*(B₀+Bₙ), by positivity, ?_⟩
  intro σ hσ q hq r
  apply (le_div_iff₀ (pow_pos (by positivity : (0:ℝ) < 1+|r|) n)).2
  have hsmall := h₀ σ hσ q hq r
  simp only [pow_zero, one_mul] at hsmall
  have hlarge := hₙ σ hσ q hq r
  by_cases hr : |r| ≤ 1
  · have hp : (1+|r|)^n ≤ (2:ℝ)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ B₀ * 2^n := mul_le_mul hsmall hp (by positivity) hB₀
      _ ≤ 2^n * (B₀+Bₙ) := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]
  · have hr' : 1 ≤ |r| := (not_le.mp hr).le
    have hp : (1+|r|)^n ≤ (2*|r|)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ ‖mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ) + r*Complex.I)‖ * (2*|r|)^n :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = 2^n * (|r|^n * ‖mellin (fun y => (dampedCutoff ψ q y : ℂ))
          ((σ : ℂ) + r*Complex.I)‖) := by rw [mul_pow]; ring
      _ ≤ 2^n * Bₙ := mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ ≤ 2^n*(B₀+Bₙ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Absolute convergence on every Mellin source line, including negative real parts. -/
theorem dampedCutoff_mellinConvergent {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a)
    (hs : tsupport ψ ⊆ Icc a b) (q : ℝ) (s : ℂ) :
    MellinConvergent (fun y => (dampedCutoff ψ q y : ℂ)) s := by
  let f : ℝ → ℂ := fun y => (y : ℂ)^(s-1) * (dampedCutoff ψ q y : ℂ)
  have hc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply continuousAt_const.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℂ))
      filter_upwards [Iio_mem_nhds ha] with y hy
      have hz : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun hh => (not_le.mpr hy) (hs hh).1)
      simp [f, dampedCutoff, hz]
    · exact (Complex.continuousAt_ofReal_cpow_const x (s-1) (Or.inr hx)).mul
        (Complex.continuous_ofReal.continuousAt.comp
          (dampedCutoff_contDiff hψ q).continuous.continuousAt)
  have hf : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc a b))
    intro y hy
    have hz : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hy (hs hh))
    simp [f, dampedCutoff, hz]
  exact (hc.integrable_of_hasCompactSupport hf).integrableOn

/-- Absolute integrability of the full vertical transform, with no frequency truncation. -/
theorem dampedCutoff_integrable_mellin_line {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (σ q : ℝ) :
    Integrable (fun r : ℝ => mellin (fun y => (dampedCutoff ψ q y : ℂ))
      ((σ : ℂ) + r*Complex.I)) := by
  have hs' : HasCompactSupport (fun u => (dampedMellinLift ψ σ q u : ℂ)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ((tsupport_comp_subset
      (g := fun y : ℝ => (y : ℂ)) rfl _).trans (dampedMellinLift_tsupport ha hb hs σ q))
  let g : SchwartzMap ℝ ℂ := hs'.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (dampedMellinLift_contDiff hψ σ q))
  have hi := (𝓕 g : SchwartzMap ℝ ℂ).integrable.comp_div (by positivity : 2*Real.pi ≠ 0)
  convert hi using 1
  funext r
  exact dampedCutoff_mellin_eq_fourier ψ σ q r

/-- Mellin inversion on every real source line. Both convergence hypotheses
are proved for the actual damped cutoff. -/
theorem dampedCutoff_mellin_inversion {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (σ q : ℝ) {x : ℝ} (hx : 0 < x) :
    (dampedCutoff ψ q x : ℂ) = ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
      (x : ℂ)^(-((σ : ℂ)+r*Complex.I)) *
        mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+r*Complex.I) := by
  have h := mellinInv_mellin_eq σ (fun y => (dampedCutoff ψ q y : ℂ)) hx
    (dampedCutoff_mellinConvergent hψ ha hs q σ)
    (dampedCutoff_integrable_mellin_line hψ ha hb hs σ q)
    (Complex.continuous_ofReal.continuousAt.comp
      (dampedCutoff_contDiff hψ q).continuous.continuousAt)
  rw [mellinInv] at h
  simpa only [Complex.real_smul, smul_eq_mul] using h.symm

/-- Every fixed polynomial weight has a uniformly bounded vertical L¹ mass. -/
theorem dampedCutoff_uniform_mellin_weighted_L1 {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b)
    (hs : tsupport ψ ⊆ Icc a b) (s₀ s₁ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc s₀ s₁, ∀ q : ℝ, 0 ≤ q →
      Integrable (fun r : ℝ => (1+|r|)^n *
        ‖mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+r*Complex.I)‖) ∧
      (∫ r : ℝ, (1+|r|)^n *
        ‖mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+r*Complex.I)‖) ≤ C := by
  obtain ⟨B,hB,h⟩ := dampedCutoff_uniform_mellin_decay hψ ha hb hs s₀ s₁ (n+2)
  refine ⟨B*Real.pi, by positivity, ?_⟩
  intro σ hσ q hq
  let F : ℝ → ℝ := fun r => (1+|r|)^n *
    ‖mellin (fun y => (dampedCutoff ψ q y : ℂ)) ((σ : ℂ)+r*Complex.I)‖
  have hFn (r : ℝ) : 0 ≤ F r := by dsimp [F]; positivity
  have hbound (r : ℝ) : F r ≤ B * (1+r^2)⁻¹ := by
    have hp : 0 < 1+|r| := by positivity
    have hd := (le_div_iff₀ (pow_pos hp (n+2))).mp (h σ hσ q hq r)
    have hw : F r ≤ B/(1+|r|)^2 := by
      apply (le_div_iff₀ (pow_pos hp 2)).2
      simpa only [F, pow_add, mul_assoc, mul_left_comm, mul_comm] using hd
    have hsquare : 1+r^2 ≤ (1+|r|)^2 := by nlinarith [sq_abs r, abs_nonneg r]
    exact hw.trans (by simpa only [div_eq_mul_inv] using
      (div_le_div_of_nonneg_left hB (by positivity : (0:ℝ) < 1+r^2) hsquare))
  have hmajor : Integrable (fun r : ℝ => B*(1+r^2)⁻¹) := integrable_inv_one_add_sq.const_mul B
  have hFm : AEStronglyMeasurable F :=
    (show Continuous (fun r : ℝ => (1+|r|)^n) by fun_prop).aestronglyMeasurable.mul
      (dampedCutoff_integrable_mellin_line hψ ha hb hs σ q).norm.aestronglyMeasurable
  have hFi : Integrable F := hmajor.mono' hFm (Filter.Eventually.of_forall (fun r => by
    rw [Real.norm_of_nonneg (hFn r)]
    exact hbound r))
  refine ⟨hFi, ?_⟩
  calc
    (∫ r : ℝ, F r) ≤ ∫ r : ℝ, B*(1+r^2)⁻¹ := integral_mono hFi hmajor hbound
    _ = B*Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

end MathCollab.Density.Stronger
