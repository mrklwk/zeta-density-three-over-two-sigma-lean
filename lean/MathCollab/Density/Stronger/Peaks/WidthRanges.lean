module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/PEAK_AGGREGATION_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
PointMeanInput and LocalMeanPacketInput remain explicit unproved analytic inputs.
No unconditional high-value, twelfth-moment or stronger-density bound is asserted.
-/
public import MathCollab.Density.Stronger.Peaks.ClusterCount

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology Finset
open scoped Interval
open MathCollab.Density MathCollab.Density.Stronger
open TaoTrudgianYang2025 (eventually_const_log_pow_le_rpow
  eventually_const_height_log_pow_mul_rpow_le_rpow
  eventually_pointValue_sixth_power_source_range)
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Peaks


theorem eventually_pointValue_log_scales {P K q : ℝ}
    (hK : 0 < K) (hq : 0 < q) :
    ∀ᶠ H : ℝ in atTop, 20 ≤ H ∧ 1 ≤ Real.log (3*H) ∧
      2*P ≤ K*Real.log (3*H) ∧ 2*(Real.log (3*H))^2 ≤ H^q := by
  have hsmall := eventually_const_log_pow_le_rpow (8:ℝ) (by norm_num) 2 hq
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (2*P/K)))
  filter_upwards [hsmall,hlog,eventually_ge_atTop (20:ℝ)] with H hs hl hH
  have hH0 : 0 < H := by linarith
  have hmono : Real.log H ≤ Real.log (3*H) :=
    Real.log_le_log hH0 (by linarith)
  have hlog3 : Real.log 3 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by linarith)
  have hupper : Real.log (3*H) ≤ 2*Real.log H := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    linarith
  have hP : 2*P/K ≤ Real.log (3*H) :=
    ((le_max_right _ _).trans hl).trans hmono
  have hPmul := (div_le_iff₀ hK).mp hP
  have hp := pow_le_pow_left₀
    (Real.log_nonneg (by linarith : 1 ≤ 3*H)) hupper 2
  refine ⟨hH,((le_max_left _ _).trans hl).trans hmono,by nlinarith,?_⟩
  nlinarith

theorem pointValueWidth_error_absorption {P C K L V : ℝ}
    (hP : 0 < P) (hK : 0 < K) (hL : 0 < L) (hKsize : 16*P*C ≤ K) :
    C*(V^2/(K*L^2))*L ≤ V^2/(16*P*L) := by
  have hc : C/K ≤ 1/(16*P) :=
    (div_le_div_iff₀ hK (by positivity)).mpr (by nlinarith)
  calc
    C*(V^2/(K*L^2))*L = (C/K)*(V^2/L) := by field_simp
    _ ≤ (1/(16*P))*(V^2/L) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = V^2/(16*P*L) := by field_simp

theorem pointValueWidth_count_identity {P K L V H : ℝ}
    (hP : 0 < P) (hL : 0 < L) (hV : 0 < V) :
    H/((V^2/(K*L^2))*(V^2/(16*P*L))^2) +
        H^2/(V^2/(16*P*L))^6 =
      K*(16*P)^2*(H*L^4/V^6) + (16*P)^6*(H^2*L^6/V^12) := by
  field_simp

theorem exists_pointValue_card_le_source_range
    (hPointMean : PointMeanInput) (hPacket : LocalMeanPacketInput)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hδUpper : δ ≤ 1/4)
    (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ K D H₀ : ℝ, 0 < K ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < V →
        K*(Real.log (3*H))^2*(2*H)^(1/4+κ) ≤ V^2 →
        V^2 ≤ K*(Real.log (3*H))^2*H^(1/2-δ) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H*(Real.log (3*H))^4/V^6 + H^2*(Real.log (3*H))^6/V^12) := by
  obtain ⟨P,C,D,B,hP,hC,hD,hB,hcount⟩ :=
    (exists_pointValue_card_le_with_width hPointMean hPacket) hδ hκ hν
  let K : ℝ := 16*P*C+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKsize : 16*P*C ≤ K := by dsimp only [K]; linarith
  have hq : 0 < (1/4:ℝ)+κ := by linarith
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp
    (eventually_pointValue_log_scales (P := P) hK hq)
  let D₁ : ℝ := D*(K*(16*P)^2+(16*P)^6)
  have hD₁ : 0 < D₁ := by dsimp only [D₁]; positivity
  refine ⟨K,D₁,max B B₁,hK,hD₁,le_max_of_le_left hB,?_⟩
  intro H V W hH hV hLower hUpper hsep hrange hlarge
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  obtain ⟨hH20,hL1,hPL,hlogFit⟩ := hB₁ H ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  let L : ℝ := Real.log (3*H)
  let G : ℝ := V^2/(K*L^2)
  have hL : 0 < L := by dsimp only [L]; linarith
  have hDen : 0 < K*L^2 := by positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hGlo : (2*H)^(1/4+κ) ≤ G := by
    dsimp only [G]
    exact (le_div_iff₀ hDen).mpr (by simpa only [L,mul_comm] using hLower)
  have hGhi : G ≤ H^(1/2-δ) := by
    dsimp only [G]
    exact (div_le_iff₀ hDen).mpr (by simpa only [L,mul_comm] using hUpper)
  have hGH : G ≤ H := by
    calc
      G ≤ H^(1/2-δ) := hGhi
      _ ≤ H^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = H := Real.rpow_one H
  have hfit : 2*(Real.log (3*H))^2 ≤ G :=
    hlogFit.trans ((Real.rpow_le_rpow hH0.le (by linarith) hq.le).trans hGlo)
  have hwidth : ∀ t : ℝ, H ≤ t → t ≤ 2*H →
      t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G := by
    intro t htlo hthi
    have ht0 : 0 ≤ t := hH0.le.trans htlo
    refine ⟨?_,?_,?_⟩
    · calc
        t^δ ≤ (2*H)^δ := Real.rpow_le_rpow ht0 hthi hδ.le
        _ ≤ (2*H)^(1/4+κ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ G := hGlo
    · exact hGhi.trans (Real.rpow_le_rpow hH0.le htlo (by linarith))
    · exact (Real.rpow_le_rpow ht0 hthi hq.le).trans hGlo
  have hOnePow : 1 ≤ (2*H)^(1/4+κ) :=
    Real.one_le_rpow (by linarith) hq.le
  have hLowerSimple : K*L^2 ≤ V^2 := by
    have hm := mul_le_mul_of_nonneg_left hOnePow hDen.le
    have hLower' : K*L^2*(2*H)^(1/4+κ) ≤ V^2 := hLower
    nlinarith
  have hVsize : 2*P*Real.log (3*H) ≤ V^2 := by
    have hm := mul_le_mul_of_nonneg_right hPL hL.le
    change 2*P*L ≤ V^2
    change 2*P*L ≤ K*L*L at hm
    nlinarith
  have herr : C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) :=
    pointValueWidth_error_absorption hP hK hL hKsize
  have hc := hcount H G V W hHB hG hGH hV hfit hwidth hVsize herr
    hsep hrange hlarge
  have he := pointValueWidth_count_identity (K := K) (H := H) hP hL hV
  change H/(G*(V^2/(16*P*L))^2)+H^2/(V^2/(16*P*L))^6 = _ at he
  change (W.card:ℝ) ≤ D*H^ν*(H/(G*(V^2/(16*P*L))^2)+H^2/(V^2/(16*P*L))^6) at hc
  rw [he] at hc
  have hx : 0 ≤ H*L^4/V^6 := by positivity
  have hy : 0 ≤ H^2*L^6/V^12 := by positivity
  have hkx : 0 ≤ K*(16*P)^2 := by positivity
  have hky : 0 ≤ (16*P)^6 := by positivity
  calc
    (W.card:ℝ) ≤ D*H^ν*
        (K*(16*P)^2*(H*L^4/V^6)+(16*P)^6*(H^2*L^6/V^12)) := hc
    _ ≤ D*H^ν*((K*(16*P)^2+(16*P)^6)*
        (H*L^4/V^6+H^2*L^6/V^12)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hkx hy,mul_nonneg hky hx]
    _ = D₁*H^ν*(H*(Real.log (3*H))^4/V^6+H^2*(Real.log (3*H))^6/V^12) := by
      dsimp only [D₁,L]
      ring



theorem eventually_pointValue_source_lower_range {K η : ℝ}
    (hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      K*(Real.log (3*H))^2*(2*H)^(1/4+η) ≤
        (H^(1/8+η))^2 := by
  have hs := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := K*2^((1/4:ℝ)+η)) (a := 1/4+η) (b := 1/4+2*η)
    (by positivity) 2 (by linarith)
  filter_upwards [hs,eventually_gt_atTop (0:ℝ)] with H hs hH
  have hp : (H^(1/8+η))^2 = H^(1/4+2*η) := by
    rw [← Real.rpow_mul_natCast hH.le]
    congr 1
    norm_num
    ring
  rw [hp,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH.le]
  nlinarith [hs]

theorem pointValue_count_mul_twelfth_identity {D H L V η : ℝ}
    (hV : 0 < V) :
    (D*H^η*(H*L^4/V^6+H^2*L^6/V^12))*V^12 =
      D*H^η*(H*L^4*V^6+H^2*L^6) := by
  field_simp

theorem pointValue_count_mul_twelfth_le_growth {D H L V η : ℝ}
    (hD : 0 ≤ D) (hH : 0 < H)
    (hV : 0 ≤ V) (hGrowth : V ≤ H^(1/6+η)) :
    D*H^η*(H*L^4*V^6+H^2*L^6) ≤
      D*L^4*H^(2+7*η)+D*L^6*H^(2+η) := by
  have hp : V^6 ≤ H^(1+6*η) := by
    have hh := pow_le_pow_left₀ hV hGrowth 6
    rw [← Real.rpow_mul_natCast hH.le] at hh
    convert hh using 1
    congr 1
    norm_num
    ring
  calc
    _ ≤ D*H^η*(H*L^4*H^(1+6*η)+H^2*L^6) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ H*L^4 by positivity)
      linarith
    _ = D*L^4*H^(2+7*η)+D*L^6*H^(2+η) := by
      have h1 : H^η*H*H^(1+6*η) = H^(2+7*η) := by
        calc
          H^η*H*H^(1+6*η) = H^(η+1)*H^(1+6*η) := by
            rw [Real.rpow_add hH η 1,Real.rpow_one]
          _ = H^(2+7*η) := by
            rw [← Real.rpow_add hH]
            congr 1
            ring
      have h2 : H^η*H^2 = H^(2+η) := by
        rw [← Real.rpow_two,← Real.rpow_add hH]
        congr 1
        ring
      calc
        _ = D*L^4*(H^η*H*H^(1+6*η))+D*L^6*(H^η*H^2) := by ring
        _ = _ := by rw [h1,h2]

theorem eventually_pointValue_high_budget {D η : ℝ}
    (hD : 0 < D) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      D*(Real.log (3*H))^4*H^(2+7*η) +
        D*(Real.log (3*H))^6*H^(2+η) ≤ H^(2+8*η) := by
  have h4 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 2*D) (a := 2+7*η) (b := 2+8*η)
    (by positivity) 4 (by linarith)
  have h6 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 2*D) (a := 2+η) (b := 2+8*η)
    (by positivity) 6 (by linarith)
  filter_upwards [h4,h6] with H h4 h6
  linarith

theorem exists_pointValue_twelfth_weighted_card_le_of_inputs
    (hPointMean : PointMeanInput) (hPacket : LocalMeanPacketInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      oneSeparated W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card:ℝ)*V^12 ≤ H^(2+ε) := by
  classical
  let η : ℝ := min (ε/16) (1/1000)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηUpper : η ≤ 1/48 := (min_le_right _ _).trans (by norm_num)
  have hηε : η ≤ ε := (min_le_left _ _).trans (by linarith)
  have h8η : 8*η ≤ ε := by have hh := min_le_left (ε/16) (1/1000:ℝ); dsimp only [η]; linarith
  obtain ⟨K,D,B,hK,hD,hB,hcount⟩ :=
    exists_pointValue_card_le_source_range hPointMean hPacket
      (δ := (1/48:ℝ)) (κ := η) (ν := η)
      (by norm_num) (by norm_num) hη hη
  obtain ⟨B₁,hGrowth⟩ := eventually_atTop.mp
    (zetaMomentCriticalNorm_eventually_lt_slab_power hη)
  have hlower := eventually_pointValue_source_lower_range hK hη
  have hupper := eventually_pointValue_sixth_power_source_range hK hη hηUpper
  have hbudget := eventually_pointValue_high_budget hD hη
  obtain ⟨B₂,hB₂⟩ := eventually_atTop.mp (hlower.and (hupper.and hbudget))
  refine ⟨max B (max B₁ B₂),le_max_of_le_left hB,?_⟩
  intro H V W hH hV hVlower hsep hrange hlarge
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  have hHB₁ : B₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHB₂ : B₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith [hB.trans hHB]
  have hH1 : 1 ≤ H := by linarith [hB.trans hHB]
  obtain ⟨hl,hu,hb⟩ := hB₂ H hHB₂
  rcases W.eq_empty_or_nonempty with rfl | ⟨t,ht⟩
  · simp only [Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity
  have hVgrowth : V ≤ H^(1/6+η) :=
    (hlarge t ht).trans (hGrowth H hHB₁ t (by
      rw [abs_of_nonneg (by linarith [(hrange t ht).1] : 0 ≤ t)]
      exact (hrange t ht).2)).le
  have hVl : H^(1/8+η) ≤ V :=
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans hVlower
  have hVsq := pow_le_pow_left₀ (by positivity : 0 ≤ H^(1/8+η)) hVl 2
  have hVupper := pow_le_pow_left₀ hV.le hVgrowth 2
  have hc := hcount H V W hHB hV (hl.trans hVsq) (hVupper.trans hu.2)
    hsep hrange hlarge
  calc
    (W.card:ℝ)*V^12 ≤
        (D*H^η*(H*(Real.log (3*H))^4/V^6+H^2*(Real.log (3*H))^6/V^12))*V^12 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = D*H^η*(H*(Real.log (3*H))^4*V^6+H^2*(Real.log (3*H))^6) :=
      pointValue_count_mul_twelfth_identity hV
    _ ≤ D*(Real.log (3*H))^4*H^(2+7*η)+D*(Real.log (3*H))^6*H^(2+η) :=
      pointValue_count_mul_twelfth_le_growth hD.le hH0 hV.le hVgrowth
    _ ≤ H^(2+8*η) := hb
    _ ≤ H^(2+ε) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)


/-- Literal eventual finite-peak interface. Both native analytic producers
remain explicit parameters; all occupancy and scale aggregation is proved. -/
theorem pointValue_peak_card_of_inputs
    (hPointMean : PointMeanInput) (hPacket : LocalMeanPacketInput) :
    ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V → ∀ W : Finset ℝ,
      oneSeparated W → (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η) := by
  intro η hη
  obtain ⟨H₀,_,hbound⟩ :=
    exists_pointValue_twelfth_weighted_card_le_of_inputs hPointMean hPacket hη
  filter_upwards [eventually_ge_atTop H₀] with H hH
  intro V hV hVH W hsep hW
  exact hbound H V W hH hV hVH hsep
    (fun t ht => ⟨(hW t ht).1,(hW t ht).2.1⟩)
    (fun t ht => (hW t ht).2.2)

end MathCollab.Density.Stronger.Peaks
