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
public import MathCollab.Density.Stronger.Peaks.Clusters
public import MathCollab.Density.Stronger.FiniteOccupancy

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
theorem atkinsonLocalMeanExcess_threshold_iff {G t error Y : ℝ} (hY : 0 < Y) :
    Y ≤ atkinsonLocalMeanExcess G t error ↔
      error+Y ≤ ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2 := by
  unfold atkinsonLocalMeanExcess
  rw [le_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h
    right
    linarith
theorem exists_atkinsonLocalMeanExcess_card_le_above_fourthRoot
    (hPacket : LocalMeanPacketInput)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → separatedAt G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
      (W.card:ℝ) ≤ D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    hPacket δ κ (ν/3) hδ hκ (show 0 < ν/3 by linarith)
  refine ⟨C,hC,2*D+32*D^3,by positivity,B,hB,?_⟩
  intro H G Y W hH hG hY hSep hrange hlarge
  have hH1 : 1 ≤ H := by linarith [hB.trans hH]
  have hH0 : 0 < H := by linarith
  have hA : 0 < D*H^(ν/3) := by positivity
  have hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ A : ℝ, (∀ t ∈ U, A ≤ t ∧ t ≤ A+atkinsonAbsorptionLength (D*H^(ν/3)) G Y) →
      (∑ t ∈ U, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        (D*H^(ν/3))*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
          Real.sqrt (G*atkinsonAbsorptionLength (D*H^(ν/3)) G Y)) := by
    intro U hsub A hlocal
    have hsepU : separatedAt G U := by
      intro x hx y hy hxy
      exact hSep x (hsub hx) y (hsub hy) hxy
    exact hsource H G A (atkinsonAbsorptionLength (D*H^(ν/3)) G Y)
      U hH hG hsepU (fun t ht => hrange t (hsub ht)) hlocal
  have hc := atkinson_card_le_of_local_packets hA hH0.le hG hY
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlarge hpacket
  exact hc.trans (atkinson_count_exponent_budget hD.le hH1 hG hY hν.le)


theorem exists_pointCluster_localMean_bound
    (hPointMean : PointMeanInput) :
    ∃ P : ℝ, 0 < P ∧ ∀ (H G V : ℝ) (W : Finset ℝ) (n : ℕ),
      20 ≤ H → 0 < G → G ≤ H → 0 < V →
      2*(Real.log (3*H))^2 ≤ G →
      oneSeparated W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      n ∈ pointClusterBins H G W →
      V^2*((pointCluster H G W n).card:ℝ) ≤
        P*Real.log (3*H)*(((pointCluster H G W n).card:ℝ) +
          4*(∫ u in pointClusterCenter H G n-G..pointClusterCenter H G n+G,
            zetaMomentCriticalNorm u^2)) := by
  obtain ⟨P,hP,hsource⟩ := hPointMean
  refine ⟨P,hP,?_⟩
  intro H G V W n hH hG hGH hV hfit hsep hrange hlarge hn
  have hc := pointClusterCenter_range hG hrange hn
  have hsub := pointCluster_subset H G W n
  have hsep' : oneSeparated (pointCluster H G W n) := by
    intro x hx y hy hxy
    exact hsep x (hsub hx) y (hsub hy) hxy
  apply hsource (3*H) V (pointClusterCenter H G n) G
    ((Real.log (3*H))^2) (pointCluster H G W n)
    (by linarith) hV hG.le (sq_nonneg _) hsep'
    (pointCluster_symmetric_interval n hG (fun t ht => (hrange t ht).1))
    (by linarith [hc.1]) (by linarith [hc.2])
  · intro t ht
    have htR := hrange t (hsub ht)
    have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hmono : Real.log t ≤ Real.log (3*H) :=
      Real.log_le_log (by linarith) (by linarith)
    exact pow_le_pow_left₀ hlt hmono 2
  · linarith
  · intro t ht
    exact hlarge t (hsub ht)

theorem localMean_lower_bound_of_peak_mass
    {P L V R I : ℝ} (hP : 0 < P) (hL : 0 < L) (hR : 0 ≤ R)
    (hV : 2*P*L ≤ V^2)
    (hsource : V^2*R ≤ P*L*(R+4*I)) :
    2*R*(V^2/(16*P*L)) ≤ I := by
  have hmul := mul_le_mul_of_nonneg_right hV hR
  have hm : V^2*R ≤ 8*P*L*I := by nlinarith
  have hden : 0 < 8*P*L := by positivity
  calc
    2*R*(V^2/(16*P*L)) = (V^2*R)/(8*P*L) := by field_simp; ring
    _ ≤ I := (div_le_iff₀ hden).mpr (by nlinarith [hm])

theorem exists_pointCluster_superlevel_entry
    (hPointMean : PointMeanInput) :
    ∃ P : ℝ, 0 < P ∧
      ∀ (H G V error : ℝ) (W : Finset ℝ) (n m : ℕ),
        20 ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        n ∈ pointClusterBins H G W → 0 < m →
        m ≤ (pointCluster H G W n).card →
        2*P*Real.log (3*H) ≤ V^2 →
        error ≤ V^2/(16*P*Real.log (3*H)) →
        error+(m:ℝ)*(V^2/(16*P*Real.log (3*H))) ≤
          ∫ u in pointClusterCenter H G n-G..pointClusterCenter H G n+G,
            zetaMomentCriticalNorm u^2 := by
  obtain ⟨P,hP,hsource⟩ := (exists_pointCluster_localMean_bound hPointMean)
  refine ⟨P,hP,?_⟩
  intro H G V error W n m hH hG hGH hV hfit hsep hrange hlarge hn hm hocc hVsize herr
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith)
  have hI := localMean_lower_bound_of_peak_mass hP hL (Nat.cast_nonneg _)
    hVsize (hsource H G V W n hH hG hGH hV hfit hsep hrange hlarge hn)
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmr : (m:ℝ) ≤ ((pointCluster H G W n).card:ℝ) := by exact_mod_cast hocc
  have hA : 0 ≤ V^2/(16*P*Real.log (3*H)) := by positivity
  have hma := mul_le_mul_of_nonneg_right hmr hA
  have hmin := mul_le_mul_of_nonneg_right hm1 hA
  nlinarith



def pointClusterSuperlevel (H G : ℝ) (W : Finset ℝ) (m : ℕ) : Finset ℕ :=
  (pointClusterBins H G W).filter (fun n => m ≤ (pointCluster H G W n).card)

theorem exists_pointCluster_superlevel_count
    (hPointMean : PointMeanInput) (hPacket : LocalMeanPacketInput)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ) (m : ℕ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) → 0 < m →
        ((pointClusterSuperlevel H G W m).card:ℝ) ≤
          2*D*H^ν*
            (H/(G*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^2) +
              H^2/((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^6) := by
  obtain ⟨P,hP,hentry⟩ := (exists_pointCluster_superlevel_entry hPointMean)
  obtain ⟨C,hC,D,hD,H₀,hH₀,hcount⟩ :=
    (exists_atkinsonLocalMeanExcess_card_le_above_fourthRoot hPacket) hδ hκ hν
  refine ⟨P,C,D,H₀,hP,hC,hD,hH₀,?_⟩
  intro H G V W m hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge hm
  let A : ℝ := V^2/(16*P*Real.log (3*H))
  let Y : ℝ := (m:ℝ)*A
  let S : Finset ℕ := pointClusterSuperlevel H G W m
  have hHlarge : 20 ≤ H := by linarith [hH₀.trans hH]
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hcolor : ∀ e : ℕ,
      ((S.filter (fun n => n%2 = e)).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
    intro e
    let U := S.filter (fun n => n%2 = e)
    have hbase : ∀ n ∈ U, n ∈ pointClusterBins H G W := by
      intro n hn
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hcentersSep := pointClusterCenters_separated (H := H) hG U e
      (fun n hn => (Finset.mem_filter.mp hn).2)
    have hcentersRange : ∀ t ∈ pointClusterCenters H G U,
        H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G := by
      intro t ht
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
      have hc := pointClusterCenter_range hG hrange (hbase n hn)
      exact ⟨hc.1,hc.2,hwidth _ hc.1 hc.2⟩
    have hcentersLarge : ∀ t ∈ pointClusterCenters H G U,
        Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t) := by
      intro t ht
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
      have hc := pointClusterCenter_range hG hrange (hbase n hn)
      have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
      have hocc : m ≤ (pointCluster H G W n).card := (Finset.mem_filter.mp hnS).2
      have hlog : Real.log (pointClusterCenter H G n) ≤ Real.log (3*H) :=
        Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
      have herror : C*G*Real.log (pointClusterCenter H G n) ≤ A :=
        (mul_le_mul_of_nonneg_left hlog (by positivity)).trans herr
      apply (atkinsonLocalMeanExcess_threshold_iff hY).mpr
      exact hentry H G V (C*G*Real.log (pointClusterCenter H G n))
        W n m hHlarge hG hGH hV hfit hsep hrange hlarge
        (hbase n hn) hm hocc hVsize herror
    have hb := hcount H G Y (pointClusterCenters H G U)
      hH hG hY hcentersSep hcentersRange hcentersLarge
    simpa only [pointClusterCenters_card hG, U] using hb
  have hcards : (S.card:ℝ) = ((S.filter (fun n => n%2 = 0)).card:ℝ) +
      ((S.filter (fun n => n%2 = 1)).card:ℝ) := by
    exact_mod_cast card_eq_sum_parity_cards S
  change (S.card:ℝ) ≤ 2*D*H^ν*(H/(G*Y^2)+H^2/Y^6)
  rw [hcards]
  have h0 := hcolor 0
  have h1 := hcolor 1
  linarith

theorem occupancy_inverse_power_budget {H G A m : ℝ}
    (hG : 0 < G) (hA : 0 < A) (hm : 1 ≤ m) :
    H/(G*(m*A)^2)+H^2/(m*A)^6 ≤
      (H/(G*A^2)+H^2/A^6)/m^2 := by
  have hm0 : 0 < m := by linarith
  have hp : m^2 ≤ m^6 := pow_le_pow_right₀ hm (by omega)
  rw [mul_pow, mul_pow]
  calc
    H/(G*(m^2*A^2))+H^2/(m^6*A^6) ≤
        H/(G*(m^2*A^2))+H^2/(m^2*A^6) := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_left (sq_nonneg H) (by positivity)
          (mul_le_mul_of_nonneg_right hp (by positivity)))
    _ = (H/(G*A^2)+H^2/A^6)/m^2 := by field_simp

theorem exists_pointValue_card_le_with_width
    (hPointMean : PointMeanInput) (hPacket : LocalMeanPacketInput)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H/(G*(V^2/(16*P*Real.log (3*H)))^2) +
            H^2/(V^2/(16*P*Real.log (3*H)))^6) := by
  obtain ⟨P,C,D,H₀,hP,hC,hD,hH₀,hcount⟩ :=
    (exists_pointCluster_superlevel_count hPointMean hPacket) hδ hκ hν
  refine ⟨P,C,4*D,H₀,hP,hC,by positivity,hH₀,?_⟩
  intro H G V W hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge
  let A : ℝ := V^2/(16*P*Real.log (3*H))
  let B : ℝ := 2*D*H^ν*(H/(G*A^2)+H^2/A^6)
  have hHpos : 0 < H := by linarith [hH₀.trans hH]
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith [hH₀.trans hH])
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsuper : ∀ m : ℕ, 0 < m →
      (((pointClusterBins H G W).filter
        (fun n => m ≤ (pointCluster H G W n).card)).card:ℝ) ≤ B/(m:ℝ)^2 := by
    intro m hm
    have hc := hcount H G V W m hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge hm
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hp := occupancy_inverse_power_budget (H := H) hG hA hm1
    calc
      _ ≤ 2*D*H^ν*(H/(G*((m:ℝ)*A)^2)+H^2/((m:ℝ)*A)^6) := hc
      _ ≤ 2*D*H^ν*((H/(G*A^2)+H^2/A^6)/(m:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = B/(m:ℝ)^2 := by dsimp only [B]; ring
  have hsum := sum_nat_occupancy_le_of_superlevels
    (pointClusterBins H G W) (fun n => (pointCluster H G W n).card) hB hsuper
  have hpartition : (W.card:ℝ) = ∑ n ∈ pointClusterBins H G W,
      ((pointCluster H G W n).card:ℝ) := by
    exact_mod_cast pointCluster_card_partition H G W
  rw [← hpartition] at hsum
  calc
    (W.card:ℝ) ≤ 2*B := hsum
    _ = (4*D)*H^ν*(H/(G*A^2)+H^2/A^6) := by dsimp only [B]; ring


end MathCollab.Density.Stronger.Peaks
