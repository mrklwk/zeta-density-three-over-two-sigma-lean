module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.SmoothExpansion
public import MathCollab.Density.Stronger.InitialDetector
public import MathCollab.Density.Stronger.DampedCutoff
public import MathCollab.Density.Stronger.SmoothMellinIdentity
public import Mathlib.Analysis.Complex.ExponentialBounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace MathCollab.Density.Stronger

def smoothDetectorBlock (ρ : ℂ) (X Y : ℝ) (j : ℤ) : ℂ :=
  smoothDyadicBlock (detectorTerm ρ X Y) j

theorem summable_norm_detectorTerm {ρ : ℂ} (X : ℝ) {Y : ℝ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ => ‖detectorTerm ρ X Y n‖) :=
  (summable_zeta_detector_series X hY hρ).norm

theorem summable_norm_detectorTerm_tail {ρ : ℂ} (X : ℝ) {Y : ℝ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ => ‖detectorTerm ρ X Y (n+2)‖) :=
  (summable_nat_add_iff 2).mpr (summable_norm_detectorTerm X hY hρ)

theorem summable_norm_smoothDetectorBlock {ρ : ℂ} (X : ℝ) {Y : ℝ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    Summable (fun j : ℤ => ‖smoothDetectorBlock ρ X Y j‖) :=
  summable_norm_smoothDyadicBlock (summable_norm_detectorTerm_tail X hY hρ)

/-- The actual exponential detector after removing n=1 equals the full smooth
dyadic series, with absolute summability proved first. -/
theorem tsum_smoothDetectorBlock {ρ : ℂ} (X : ℝ) {Y : ℝ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    (∑' j : ℤ, smoothDetectorBlock ρ X Y j) = detectorTail ρ X Y :=
  tsum_smoothDyadicBlock (summable_norm_detectorTerm_tail X hY hρ)

theorem smoothDetectorBlock_zero_of_nonpos (ρ : ℂ) (X Y : ℝ) {j : ℤ} (hj : j ≤ 0) :
    smoothDetectorBlock ρ X Y j = 0 := smoothDyadicBlock_zero_of_nonpos _ hj

/-- Vanishing of small smooth blocks uses the exact Mobius cancellation.
The removed n=1 term cannot enter this statement. -/
theorem smoothDetectorBlock_zero_of_small (ρ : ℂ) (X Y : ℝ) {j : ℤ}
    (hj : (2 : ℝ)^j ≤ X/2) : smoothDetectorBlock ρ X Y j = 0 := by
  suffices hz : ∀ n : ℕ, smoothDyadicTerm (detectorTerm ρ X Y) n j = 0 by
    simp only [smoothDetectorBlock, smoothDyadicBlock, hz, tsum_zero]
  intro n
  by_cases hn : ((n+2 : ℕ) : ℝ) ≤ X
  · have hc := mollifierCoefficient_vanishes (by omega : 2 ≤ n+2) hn
    simp only [smoothDyadicTerm, detectorTerm, hc, Int.cast_zero, zero_mul]
  · have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
    have hr : (3/2 : ℝ) ≤ ((n+2 : ℕ) : ℝ)/(2 : ℝ)^j :=
      (le_div_iff₀ hp).mpr (by nlinarith)
    simp only [smoothDyadicTerm, smoothDyadicWeight_zero_of_ge hr,
      Complex.ofReal_zero, mul_zero]

/-- The bound is on the sum of norms, as required for truncating dyadic
scales; a bound merely on the norm of the original tail would not suffice. -/
theorem tsum_norm_detector_tail_le {ρ : ℂ} (X : ℝ) {Y : ℝ} (K : ℕ)
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    (∑' n : ℕ, ‖detectorTerm ρ X Y (n+K)‖) ≤
      (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/Y)*(1-Real.exp (-1/Y))⁻¹ := by
  let r := Real.exp (-1/Y)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hY)
  have hg := (hasSum_geometric_of_lt_one hr hr').mul_left
    ((⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/Y))
  have hb (n : ℕ) : ‖detectorTerm ρ X Y (n+K)‖ ≤
      (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/Y)*r^n := by
    have he : Real.exp (-((n+K : ℕ) : ℝ)/Y) = Real.exp (-(K : ℝ)/Y)*r^n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    exact (norm_detectorTerm_le X (n+K) hρ).trans_eq (by rw [he]; ring)
  have hn := hg.summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
  exact (hn.tsum_le_tsum hb hg.summable).trans_eq hg.tsum_eq

/-- A real threshold tail is bounded by any earlier integer tail. -/
theorem shifted_indicator_tail_le {f : ℕ → ℝ} (hf : Summable f)
    (hf0 : ∀ n, 0 ≤ f n) {r : ℝ} {K : ℕ} (hK : (K : ℝ) ≤ r) :
    (∑' n : ℕ, if r < ((n+2 : ℕ) : ℝ) then f (n+2) else 0) ≤
      ∑' n : ℕ, f (n+K) := by
  let g : ℕ → ℝ := fun n => if r < (n : ℝ) then f n else 0
  have hg0 (n : ℕ) : 0 ≤ g n := by dsimp [g]; split_ifs <;> simp [hf0]
  have hgle (n : ℕ) : g n ≤ f n := by dsimp [g]; split_ifs <;> simp [hf0]
  have hg : Summable g := hf.of_nonneg_of_le hg0 hgle
  have h2 := hg.sum_add_tsum_nat_add 2
  have hstart : (∑' n : ℕ, g (n+2)) ≤ ∑' n : ℕ, g n := by
    rw [← h2]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ => hg0 n))
  have hzero : (∑ n ∈ Finset.range K, g n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnR : (n : ℝ) < K := by exact_mod_cast Finset.mem_range.mp hn
    exact ite_eq_right (not_lt.mpr (hnR.le.trans hK))
  have he : (∑' n : ℕ, g n) = ∑' n : ℕ, g (n+K) := by
    simpa only [hzero, zero_add] using (hg.sum_add_tsum_nat_add K).symm
  exact hstart.trans (he.le.trans
    (((summable_nat_add_iff K).mpr hg).tsum_le_tsum (fun n => hgle (n+K))
      ((summable_nat_add_iff K).mpr hf)))

theorem smoothDetectorBlock_scale_tail_bound {ρ : ℂ} (X : ℝ) {Y R : ℝ} (K : ℕ)
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) (hK : (K : ℝ) ≤ R/2) :
    (∑' j : ℤ, if R < (2 : ℝ)^j then ‖smoothDetectorBlock ρ X Y j‖ else 0) ≤
      (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/Y)*(1-Real.exp (-1/Y))⁻¹ := by
  have h1 := smoothDyadicBlock_scale_tail_le (summable_norm_detectorTerm_tail X hY hρ) R
  have h2 := shifted_indicator_tail_le (summable_norm_detectorTerm X hY hρ)
    (fun n => norm_nonneg (detectorTerm ρ X Y n)) hK
  exact h1.trans (h2.trans (tsum_norm_detector_tail_le X K hY hρ))

/-- Quantitative truncation of the dyadic scales for arbitrary independent
scales X,Y in the required range. The cutoff does not enter the smooth weight. -/
theorem smoothDetectorBlock_scale_tail_le_two_rpow {ρ : ℂ} {X Y T : ℝ}
    (hT : 1 ≤ T) (hlog : 16 ≤ Real.log T) (hX : 0 ≤ X) (hXT : X ≤ T)
    (hY : 1 ≤ Y) (hYT : Y ≤ T) (hρ : 0 ≤ ρ.re) :
    (∑' j : ℤ, if Y*(Real.log T)^2 < (2 : ℝ)^j
      then ‖smoothDetectorBlock ρ X Y j‖ else 0) ≤ 2*T^(-2 : ℝ) := by
  let R := Y*(Real.log T)^2
  let K := ⌊R/2⌋₊
  have hTpos : 0 < T := by linarith
  have hYpos : 0 < Y := by linarith
  have hR : 4 ≤ R := by dsimp [R]; nlinarith
  have hK : (K : ℝ) ≤ R/2 := Nat.floor_le (by linarith)
  have hKlo : R/4 ≤ (K : ℝ) := by
    have hh := Nat.lt_floor_add_one (R/2)
    change R/2 < (K : ℝ)+1 at hh
    linarith
  have hexp : Real.exp (-(K : ℝ)/Y) ≤ T^(-4 : ℝ) := by
    rw [Real.rpow_def_of_pos hTpos]
    apply Real.exp_le_exp.mpr
    have hh : (Real.log T)^2/4 ≤ (K : ℝ)/Y := by
      apply (le_div_iff₀ hYpos).mpr
      dsimp [R] at hKlo
      nlinarith
    rw [neg_div]
    nlinarith [mul_nonneg (show 0 ≤ Real.log T by linarith)
      (show 0 ≤ Real.log T-16 by linarith)]
  have hb := smoothDetectorBlock_scale_tail_bound X K hYpos hρ hK
  have hgeom : 0 ≤ (1-Real.exp (-1/Y))⁻¹ := by
    apply inv_nonneg.mpr
    have hh := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) hYpos)
    linarith
  calc
    _ ≤ (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/Y)*(1-Real.exp (-1/Y))⁻¹ := hb
    _ ≤ T*T^(-4 : ℝ)*(2*T) := by
      apply mul_le_mul _ ((detector_geometric_factor_le hY).trans (by linarith))
        hgeom (by positivity)
      exact mul_le_mul ((Nat.floor_le hX).trans hXT) hexp (by positivity) (by positivity)
    _ = 2*T^(-2 : ℝ) := by
      have he : T^(-4 : ℝ)*T^2 = T^(-2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hTpos]
        norm_num
      nlinarith [he]

/-- Fixed finite list of all nonnegative dyadic scales at most R. -/
def smoothScaleIndices (R : ℝ) : Finset ℤ :=
  (Finset.Icc 0 ⌈Real.log R/Real.log 2⌉).filter (fun j => (2 : ℝ)^j ≤ R)

theorem mem_smoothScaleIndices {R : ℝ} {j : ℤ} :
    j ∈ smoothScaleIndices R ↔ 0 ≤ j ∧ (2 : ℝ)^j ≤ R := by
  constructor
  · intro hj
    obtain ⟨hmem, hscale⟩ := Finset.mem_filter.mp hj
    exact ⟨(Finset.mem_Icc.mp hmem).1, hscale⟩
  · rintro ⟨hj, hscale⟩
    have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
    have hl := Real.log_le_log hp hscale
    rw [Real.log_zpow] at hl
    have hjR : (j : ℝ) ≤ Real.log R/Real.log 2 :=
      (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl
    have hjceil : j ≤ ⌈Real.log R/Real.log 2⌉ := by
      exact_mod_cast hjR.trans (Int.le_ceil (Real.log R/Real.log 2))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj, hjceil⟩, hscale⟩

theorem smoothScaleIndices_nonempty {R : ℝ} (hR : 1 ≤ R) :
    (smoothScaleIndices R).Nonempty := by
  refine ⟨0, mem_smoothScaleIndices.mpr ?_⟩
  simpa only [zpow_zero] using And.intro (le_refl (0 : ℤ)) hR

theorem smoothScaleIndices_card_le {R : ℝ} (hR : 1 ≤ R) :
    ((smoothScaleIndices R).card : ℝ) ≤ Real.log R/Real.log 2+2 := by
  have hlog : 0 ≤ Real.log R/Real.log 2 :=
    div_nonneg (Real.log_nonneg hR) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hc : (0 : ℤ) ≤ ⌈Real.log R/Real.log 2⌉ := by
    have hh := Int.ceil_mono hlog
    simpa only [Int.ceil_zero] using hh
  have hcard := Finset.card_le_card (Finset.filter_subset
    (fun j : ℤ => (2 : ℝ)^j ≤ R) (Finset.Icc 0 ⌈Real.log R/Real.log 2⌉))
  have hcardR : ((smoothScaleIndices R).card : ℝ) ≤
      ((Finset.Icc (0 : ℤ) ⌈Real.log R/Real.log 2⌉).card : ℝ) := by exact_mod_cast hcard
  have he : ((Finset.Icc (0 : ℤ) ⌈Real.log R/Real.log 2⌉).card : ℝ) =
      (⌈Real.log R/Real.log 2⌉ : ℝ)+1 := by
    rw [Int.card_Icc]
    norm_num only [sub_zero]
    have hh := Int.toNat_of_nonneg (show (0 : ℤ) ≤ ⌈Real.log R/Real.log 2⌉+1 by omega)
    exact_mod_cast hh
  rw [he] at hcardR
  have hceil := Int.ceil_lt_add_one (Real.log R/Real.log 2)
  linarith

theorem smoothDetectorBlock_norm_partition {ρ : ℂ} (X : ℝ) {Y : ℝ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) (R : ℝ) :
    (∑' j : ℤ, ‖smoothDetectorBlock ρ X Y j‖) =
      (∑ j ∈ smoothScaleIndices R, ‖smoothDetectorBlock ρ X Y j‖) +
      ∑' j : ℤ, if R < (2 : ℝ)^j then ‖smoothDetectorBlock ρ X Y j‖ else 0 := by
  classical
  let f := fun j : ℤ => ‖smoothDetectorBlock ρ X Y j‖
  let g := fun j : ℤ => if j ∈ smoothScaleIndices R then f j else 0
  let h := fun j : ℤ => if R < (2 : ℝ)^j then f j else 0
  have hf := summable_norm_smoothDetectorBlock X hY hρ
  have hg : Summable g := summable_of_ne_finset_zero (s := smoothScaleIndices R)
    (fun j hj => ite_eq_right hj)
  have hh : Summable h := hf.of_nonneg_of_le
    (fun j => by dsimp [h, f]; split_ifs <;> positivity)
    (fun j => by dsimp [h, f]; split_ifs <;> simp)
  have he (j : ℤ) : f j = g j+h j := by
    by_cases hj : j ∈ smoothScaleIndices R
    · have hle := (mem_smoothScaleIndices.mp hj).2
      simp only [g, h, ite_eq_left hj, ite_eq_right (not_lt.mpr hle), add_zero]
    · by_cases hlarge : R < (2 : ℝ)^j
      · simp only [g, h, ite_eq_right hj, ite_eq_left hlarge, zero_add]
      · have hjneg : j ≤ 0 := by
          by_contra h
          exact hj (mem_smoothScaleIndices.mpr ⟨by omega, le_of_not_gt hlarge⟩)
        simp only [g, h, ite_eq_right hj, ite_eq_right hlarge, add_zero, f,
          smoothDetectorBlock_zero_of_nonpos _ _ _ hjneg, norm_zero]
  have hgsum : (∑' j : ℤ, g j) = ∑ j ∈ smoothScaleIndices R, f j := by
    rw [tsum_eq_sum (s := smoothScaleIndices R) (fun j hj => ite_eq_right hj)]
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_left hj
  calc
    (∑' j : ℤ, f j) = ∑' j : ℤ, (g j+h j) := tsum_congr he
    _ = (∑' j : ℤ, g j)+(∑' j : ℤ, h j) := hg.tsum_add hh
    _ = _ := by rw [hgsum]

/-- Quantitative extraction from a finite list independent of the zero.
The lower bound on the chosen scale is derived from cancellation. -/
theorem exists_smoothDetectorBlock {ρ : ℂ} {X Y R A : ℝ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) (hR : 1 ≤ R) (hA : 0 < A)
    (hlarge : A ≤ ‖detectorTail ρ X Y‖)
    (htail : (∑' j : ℤ, if R < (2 : ℝ)^j then ‖smoothDetectorBlock ρ X Y j‖ else 0) ≤ A/2) :
    ∃ j ∈ smoothScaleIndices R, X/2 < (2 : ℝ)^j ∧
      A/(2*(smoothScaleIndices R).card) ≤ ‖smoothDetectorBlock ρ X Y j‖ := by
  have hJ := smoothScaleIndices_nonempty hR
  have hcard : (0 : ℝ) < (smoothScaleIndices R).card := by
    exact_mod_cast Finset.card_pos.mpr hJ
  have hbound := norm_tsum_le_tsum_norm (summable_norm_smoothDetectorBlock X hY hρ)
  rw [tsum_smoothDetectorBlock X hY hρ, smoothDetectorBlock_norm_partition X hY hρ R] at hbound
  have hsum : A/2 ≤ ∑ j ∈ smoothScaleIndices R, ‖smoothDetectorBlock ρ X Y j‖ := by linarith
  have hex : ∃ j ∈ smoothScaleIndices R,
      A/(2*(smoothScaleIndices R).card) ≤ ‖smoothDetectorBlock ρ X Y j‖ := by
    by_contra h
    push Not at h
    have hh : (∑ j ∈ smoothScaleIndices R, ‖smoothDetectorBlock ρ X Y j‖) < A/2 := by
      calc
        _ < ∑ _j ∈ smoothScaleIndices R, A/(2*(smoothScaleIndices R).card) :=
          Finset.sum_lt_sum_of_nonempty hJ h
        _ = A/2 := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp
    linarith
  obtain ⟨j, hj, hnorm⟩ := hex
  refine ⟨j, hj, ?_, hnorm⟩
  by_contra h
  have hz := smoothDetectorBlock_zero_of_small ρ X Y (le_of_not_gt h)
  rw [hz, norm_zero] at hnorm
  exact (not_le_of_gt (div_pos hA (by positivity))) hnorm

theorem smoothScaleIndices_card_le_log {T R : ℝ}
    (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T) (hR : 1 ≤ R) (hRT : R ≤ T^2) :
    ((smoothScaleIndices R).card : ℝ) ≤ 6*Real.log T := by
  have hTpos : 0 < T := by linarith
  have hl := Real.log_le_log (show 0 < R by linarith) hRT
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hratio : Real.log R/Real.log 2 ≤ 4*Real.log T := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hh := mul_le_mul_of_nonneg_left htwo (show 0 ≤ 4*Real.log T by linarith)
    nlinarith
  exact (smoothScaleIndices_card_le hR).trans (by linarith)

theorem log_sq_eventually_le_height :
    ∀ᶠ T : ℝ in atTop, (Real.log T)^2 ≤ T := by
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with T hT hlog
  have hh := (div_lt_iff₀ hT).mp hlog
  linarith

/-- All-zero smooth dyadic detection for the stronger parameters, with no
Weyl or moment premise. The finite list is chosen before rho varies. -/
theorem smoothDetector_eventually_large {σ δ : ℝ}
    (hσ : 3/4 < σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ∃ j ∈ smoothScaleIndices (detectorY σ T*(Real.log T)^2),
        detectorX δ T/2 < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤
          ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY σ T) j‖ := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 16,
    log_sq_eventually_le_height, detectorTail_eventually_large hσ hδ hδ']
    with T hT hlog hlogSq hdetect
  intro ρ hβ hβ' hγ hγ' hzero
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTpos.le _
  have hXT : detectorX δ T ≤ T := by
    simpa only [detectorX, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show δ ≤ 1 by linarith)
  have hY : 1 ≤ detectorY σ T := Real.one_le_rpow hT1 (smoothingExponent_pos hσ).le
  have hYT : detectorY σ T ≤ T := by
    simpa only [detectorY, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (smoothingExponent_lt_one hσ).le
  have hR : 1 ≤ detectorY σ T*(Real.log T)^2 := by nlinarith
  have hRT : detectorY σ T*(Real.log T)^2 ≤ T^2 := by
    calc
      _ ≤ T*T := mul_le_mul hYT hlogSq (sq_nonneg _) hTpos.le
      _ = _ := by ring
  have htail := smoothDetectorBlock_scale_tail_le_two_rpow hT1 hlog hX hXT hY hYT
    (show 0 ≤ ρ.re by linarith)
  have hsmall : 2*T^(-2 : ℝ) ≤ (1/4 : ℝ) := by
    have he : 2*T^(-2 : ℝ) = 2/T^2 := by
      rw [Real.rpow_neg hTpos.le, Real.rpow_two]
      ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hTpos)).mpr
    nlinarith
  obtain ⟨j, hj, hscale, hheight⟩ := exists_smoothDetectorBlock
    (show 0 < detectorY σ T by linarith) (show 0 ≤ ρ.re by linarith) hR
    (by norm_num : (0 : ℝ) < 1/2) (hdetect ρ hβ hβ' hγ hγ' hzero)
    (by simpa only [show (1/2 : ℝ)/2 = 1/4 by norm_num] using htail.trans hsmall)
  refine ⟨j, hj, hscale, ?_⟩
  have hcard := smoothScaleIndices_card_le_log hT1 (by linarith) hR hRT
  have hcpos : (0 : ℝ) < (smoothScaleIndices (detectorY σ T*(Real.log T)^2)).card := by
    exact_mod_cast Finset.card_pos.mpr (smoothScaleIndices_nonempty hR)
  calc
    (1/(24*Real.log T) : ℝ) ≤
        (1/2)/(2*(smoothScaleIndices (detectorY σ T*(Real.log T)^2)).card) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith
    _ ≤ _ := hheight

/-- On scales at least two, the removed n=1 term already vanishes in the
cutoff. Thus the detecting block is exactly the full block used in Mellin
inversion, with the original coefficients and q=N/Y. -/
theorem smoothDetectorBlock_eq_smoothMollifierBlock {ρ : ℂ} (X : ℝ) {Y : ℝ} {j : ℤ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) (hN : 2 ≤ (2 : ℝ)^j) :
    smoothDetectorBlock ρ X Y j =
      smoothMollifierBlock smoothDyadicWeight ρ X ((2 : ℝ)^j) ((2 : ℝ)^j/Y) := by
  let N : ℝ := (2 : ℝ)^j
  let f : ℕ → ℂ := fun n =>
    detectorTerm ρ X Y n * (smoothDyadicWeight ((n : ℝ)/N) : ℂ)
  have hNpos : 0 < N := zpow_pos (by norm_num) _
  have hfn : Summable (fun n : ℕ => ‖f n‖) := by
    apply (summable_norm_detectorTerm X hY hρ).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothDyadicWeight_bounds _).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (smoothDyadicWeight_bounds _).2
  have hf : Summable f := hfn.of_norm
  have hf0 : f 0 = 0 := by simp [f, detectorTerm, mollifierCoefficient]
  have hf1 : f 1 = 0 := by
    have hr : (1 : ℝ)/N ≤ 5/8 := (div_le_iff₀ hNpos).mpr (by dsimp [N]; nlinarith)
    simp only [f, Nat.cast_one, smoothDyadicWeight_zero_of_le hr, Complex.ofReal_zero, mul_zero]
  have hprefix : (∑ n ∈ Finset.range 2, f n) = 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf0, hf1, add_zero]
  have hseq : smoothDetectorBlock ρ X Y j = ∑' n : ℕ, f n := by
    have he := hf.sum_add_tsum_nat_add 2
    simpa only [hprefix, zero_add, smoothDetectorBlock, smoothDyadicBlock,
      smoothDyadicTerm, f, N] using he
  rw [hseq, smoothMollifierBlock]
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ (mollifierDirichletCoeff_zero X)]
  dsimp [f, detectorTerm, mollifierDirichletCoeff, dampedCutoff]
  have he : -((2 : ℝ)^j/Y)*((n : ℝ)/(2 : ℝ)^j) = -(n : ℝ)/Y := by
    field_simp [hNpos.ne']
  rw [he, Complex.ofReal_mul]
  dsimp [N]
  ring

end MathCollab.Density.Stronger
