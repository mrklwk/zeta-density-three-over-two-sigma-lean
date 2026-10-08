module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected physical-budget proofs released under MIT-0; see
../../../../../third_party/twelfth/LICENSE-MIT-0.
Source pin: 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Manifest: ../../../../../third_party/twelfth/PHYSICAL_PACKET_ASSEMBLY_MANIFEST.json.
The new assembly uses the literal native prefix/Gram bound and keeps the
actual stationary-zeta source-to-prefix inequality as an explicit premise.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSourceCutoffBound
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalizedGram
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Harmonic.Bounds
public import WeylPort.GrowthAlgebra

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology Finset
open TaoTrudgianYang2025 (eventually_const_log_pow_le_rpow)
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinson_clog_le_height_log {H : ℝ} {N : ℕ}
    (hH : 1 ≤ H) (hlog : 1 ≤ Real.log (2*H)) (hN : (N:ℝ) ≤ H) :
    (Nat.clog 2 N:ℝ) ≤ (1/Real.log 2+1)*Real.log (2*H) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hN0 : N = 0
  · subst N
    simp only [Nat.clog_zero_right, Nat.cast_zero]
    positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
  have hceil := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hN1)
  have he := Real.natCeil_logb_natCast 2 N
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hceil
  have hl : Real.log (N:ℝ) ≤ Real.log (2*H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hd := div_le_div_of_nonneg_right hl h2.le
  unfold Real.logb at hceil
  calc
    _ ≤ Real.log (2*H)/Real.log 2+Real.log (2*H) := by linarith
    _ = _ := by ring

theorem atkinson_harmonic_le_height_log {H G : ℝ} {N : ℕ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hlog : 1 ≤ Real.log (2*H))
    (hN : (N:ℝ) ≤ H) :
    (harmonic (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)):ℝ) ≤ 2*Real.log (2*H) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hs : Real.sqrt (H*(N:ℝ)) ≤ H := by
    apply (Real.sqrt_le_left hH0.le).2
    nlinarith
  have hq : Real.sqrt (H*(N:ℝ))/G ≤ H :=
    (div_le_iff₀ hG0).2 (by nlinarith)
  have hm := atkinson_harmonic_mono (Nat.ceil_mono hq)
  have hc : (Nat.ceil H:ℝ) ≤ 2*H := by
    have hh := Nat.ceil_lt_add_one hH0.le
    linarith
  have hc0 : (0:ℝ) < Nat.ceil H := hH0.trans_le (Nat.le_ceil H)
  have hl := Real.log_le_log hc0 hc
  have hb := harmonic_le_one_add_log (Nat.ceil H)
  linarith

theorem eventually_atkinson_height_log_pow_le_rpow (k : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ H : ℝ in atTop, (Real.log (2*H))^k ≤ H^ν := by
  filter_upwards [eventually_const_log_pow_le_rpow ((2:ℝ)^k) (by positivity) k hν,
    eventually_ge_atTop (2:ℝ)] with H hsmall hH
  have hH0 : 0 < H := by linarith
  have hlog2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hH
  have hlog : Real.log (2*H) ≤ 2*Real.log H := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    linarith
  have hp := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ 2*H)) hlog k
  rw [mul_pow] at hp
  exact hp.trans hsmall



theorem atkinsonPhysicalCutoff_le_natural {H G : ℝ}
    (hH : 1 ≤ H) (hG : 0 < G) (hupper : G ≤ Real.sqrt (2*H))
    (hlog : 1 ≤ Real.log (2*H)) :
    (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) ≤
      74*H*(Real.log (2*H))^2/G^2 := by
  exact (atkinsonSourceCutoff_le_natural (by linarith : 1 ≤ 2*H) hG hupper hlog).trans_eq
    (by ring)

theorem atkinsonPhysical_cutoff_scale_identity {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) (q : ℝ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^q =
      (74:ℝ)^q*H^(q-1/2)*ℓ^(2*q)*G^(2-2*q) := by
  have hbase : (74*H*ℓ^2/G^2)^q =
      (74:ℝ)^q*H^q*ℓ^(2*q)/G^(2*q) := by
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity : 0 ≤ 74*H) (sq_nonneg ℓ),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 74) hH.le,
      ← Real.rpow_natCast,← Real.rpow_mul hℓ.le,
      ← Real.rpow_natCast,← Real.rpow_mul hG.le]
    norm_num
  rw [hbase,Real.rpow_sub hH,Real.rpow_sub hG,Real.rpow_neg hH.le,Real.rpow_two]
  ring

theorem atkinsonPhysical_diagonal_scale {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/2:ℝ) ≤
      5476*(H/G)*ℓ^3 := by
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ]
  norm_num only [show (3/2:ℝ)-1/2 = 1 by norm_num,
    show 2*(3/2:ℝ) = 3 by norm_num,show 2-2*(3/2:ℝ) = -1 by norm_num,
    Real.rpow_one,Real.rpow_neg_one,Real.rpow_ofNat]
  have hc : (74:ℝ)^(3/2:ℝ) ≤ 5476 := by
    calc
      _ ≤ (74:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  calc
    _ ≤ 5476*H*ℓ^3*G⁻¹ := by gcongr
    _ = _ := by ring

theorem atkinsonPhysical_near_scale {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    (Real.sqrt H/G)*(G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(1:ℝ)) =
      74*(H/G)*ℓ^2 := by
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ]
  norm_num only [show (1:ℝ)-1/2 = 1/2 by norm_num,
    show 2*(1:ℝ) = 2 by norm_num,show 2-2*(1:ℝ) = 0 by norm_num,
    Real.rpow_one,Real.rpow_zero,Real.rpow_two,mul_one]
  rw [← Real.sqrt_eq_rpow]
  calc
    _ = 74*(Real.sqrt H)^2/G*ℓ^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hH.le]; ring

theorem atkinsonPhysical_far_scale {H G ℓ L : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 1 ≤ ℓ) :
    (H^(-(1/4:ℝ))*Real.sqrt L)*(G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/4:ℝ)) ≤
      74*Real.sqrt (G*L)*ℓ^3 := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ0]
  norm_num only [show (3/4:ℝ)-1/2 = 1/4 by norm_num,
    show 2*(3/4:ℝ) = 3/2 by norm_num,show 2-2*(3/4:ℝ) = 1/2 by norm_num]
  have hh : H^(-(1/4:ℝ))*H^(1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hH]; norm_num
  have he : (H^(-(1/4:ℝ))*Real.sqrt L)*
      ((74:ℝ)^(3/4:ℝ)*H^(1/4:ℝ)*ℓ^(3/2:ℝ)*G^(1/2:ℝ)) =
      (74:ℝ)^(3/4:ℝ)*Real.sqrt (G*L)*ℓ^(3/2:ℝ) := by
    rw [Real.sqrt_mul hG.le,Real.sqrt_eq_rpow G]
    calc
      _ = (H^(-(1/4:ℝ))*H^(1/4:ℝ))*
        ((74:ℝ)^(3/4:ℝ)*(G^(1/2:ℝ)*Real.sqrt L)*ℓ^(3/2:ℝ)) := by ring
      _ = _ := by rw [hh,one_mul]
  rw [he]
  have hc : (74:ℝ)^(3/4:ℝ) ≤ 74 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 74) (by norm_num : (3/4:ℝ) ≤ 1)
  have hl : ℓ^(3/2:ℝ) ≤ ℓ^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le
      hℓ (by norm_num : (3/2:ℝ) ≤ 3)
  gcongr



theorem atkinsonPowerGapTerm_epsilon_factor {N : ℕ} (hN : 0 < N)
    (η H G L : ℝ) (R : ℕ) :
    atkinsonPowerGapTerm η H G L N R =
      (N:ℝ)^η*atkinsonPowerGapTerm 0 H G L N R := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  unfold atkinsonPowerGapTerm
  simp only [add_zero,Real.rpow_add hN0]
  ring

theorem atkinsonPhysical_gap_term_zero_le {H G : ℝ} {N : ℕ} (L : ℝ) (R : ℕ)
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hlog : 1 ≤ Real.log (2*H))
    (hN : (N:ℝ) ≤ H) (hcut : (N:ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm 0 H G L N R ≤
      148000*(Real.log (2*H))^3*((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hlog0 : 0 < Real.log (2*H) := by linarith
  let P := G^2*H^(-(1/2:ℝ))
  let B := 74*H*(Real.log (2*H))^2/G^2
  let K := (harmonic (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)):ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hK : 0 ≤ K := by
    simpa only [harmonic_zero,Rat.cast_zero] using atkinson_harmonic_mono
      (Nat.zero_le (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)))
  have hk : K ≤ 2*Real.log (2*H) := atkinson_harmonic_le_height_log hH hG hlog hN
  have hdiag : P*(N:ℝ)^(3/2:ℝ) ≤ 5476*(H/G)*(Real.log (2*H))^3 := by
    calc
      _ ≤ P*B^(3/2:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut (by norm_num)) hP
      _ ≤ _ := atkinsonPhysical_diagonal_scale hH0 hG0 hlog0
  have hnear : (Real.sqrt H/G)*(P*(N:ℝ)^(1:ℝ)) ≤
      74*(H/G)*(Real.log (2*H))^2 := by
    calc
      _ ≤ (Real.sqrt H/G)*(P*B^(1:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut (by norm_num)) hP
      _ = _ := atkinsonPhysical_near_scale hH0 hG0 hlog0
  have hfar : (H^(-(1/4:ℝ))*Real.sqrt L)*(P*(N:ℝ)^(3/4:ℝ)) ≤
      74*Real.sqrt (G*L)*(Real.log (2*H))^3 := by
    calc
      _ ≤ (H^(-(1/4:ℝ))*Real.sqrt L)*(P*B^(3/4:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut (by norm_num)) hP
      _ ≤ _ := atkinsonPhysical_far_scale hH0 hG0 hlog
  have hd := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg R : (0:ℝ) ≤ _)
  have hn := mul_le_mul
    (mul_le_mul_of_nonneg_left hnear (by positivity : 0 ≤ 120*(R:ℝ)))
    hk hK (by positivity)
  have hf := mul_le_mul_of_nonneg_left hfar (by positivity : 0 ≤ 2000*(R:ℝ)^2)
  have hsum := add_le_add (add_le_add hd hn) hf
  have he : P*atkinsonPowerGapTerm 0 H G L N R =
      (R:ℝ)*(P*(N:ℝ)^(3/2:ℝ))+
      (120*(R:ℝ)*((Real.sqrt H/G)*(P*(N:ℝ)^(1:ℝ))))*K+
      2000*(R:ℝ)^2*((H^(-(1/4:ℝ))*Real.sqrt L)*(P*(N:ℝ)^(3/4:ℝ))) := by
    unfold atkinsonPowerGapTerm K
    simp only [add_zero]
    ring
  change P*atkinsonPowerGapTerm 0 H G L N R ≤ _
  rw [he]
  apply hsum.trans
  have hpos : 0 ≤ (R:ℝ)*(H/G)*(Real.log (2*H))^3 := by positivity
  ring_nf at hpos ⊢
  nlinarith



theorem atkinsonPhysical_gap_budget_log_le {H G η : ℝ} {N : ℕ} (L : ℝ) (R : ℕ)
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hη : 0 ≤ η) (hN0 : 0 < N)
    (hlog : 1 ≤ Real.log (2*H)) (hN : (N:ℝ) ≤ H)
    (hcut : (N:ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPowerGapBudget η H G L N R ≤
      (148000*(1/Real.log 2+1)^2)*H^η*(Real.log (2*H))^5*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hlog0 : 0 < Real.log (2*H) := by linarith
  have hterm := atkinsonPhysical_gap_term_zero_le L R hH hG hlog hN hcut
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg N) hN hη
  have hJ := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.clog 2 N) : (0:ℝ) ≤ _)
    (atkinson_clog_le_height_log hH hlog hN) 2
  have ht : G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm η H G L N R ≤
      H^η*(148000*(Real.log (2*H))^3*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L))) := by
    rw [atkinsonPowerGapTerm_epsilon_factor hN0]
    calc
      _ = (N:ℝ)^η*(G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm 0 H G L N R) := by ring
      _ ≤ (N:ℝ)^η*(148000*(Real.log (2*H))^3*
          ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L))) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
  unfold atkinsonPowerGapBudget
  calc
    _ = (Nat.clog 2 N:ℝ)^2*
      (G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm η H G L N R) := by ring
    _ ≤ (Nat.clog 2 N:ℝ)^2*
      (H^η*(148000*(Real.log (2*H))^3*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)))) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ ≤ ((1/Real.log 2+1)*Real.log (2*H))^2*
      (H^η*(148000*(Real.log (2*H))^3*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)))) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = _ := by ring

theorem exists_atkinsonPhysicalGapBudget_le_twoTerm {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G L : ℝ, ∀ R : ℕ, H₀ ≤ H → H^δ ≤ G → G ≤ Real.sqrt (2*H) →
        G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget (ν/2) H G L
            (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) R ≤
          C*H^ν*((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
  obtain ⟨A,hA,hgeometry⟩ := exists_atkinsonPhysicalCutoff_prefix_geometry hδ
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    (eventually_atkinson_height_log_pow_le_rpow 5 (show 0 < ν/2 by linarith))
  obtain ⟨D,hD⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  let C : ℝ := 148000*(1/Real.log 2+1)^2
  have hC : 0 < C := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C]
    positivity
  refine ⟨C,hC,max A (max B D),(hA.trans (le_max_left _ _)),?_⟩
  intro H G L R hH hwidth hupper
  have hAH : A ≤ H := (le_max_left _ _).trans hH
  have hBH : B ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hDH : D ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by linarith [hA.trans hAH]
  have hH0 : 0 < H := by linarith
  have hG1 : 1 ≤ G := (Real.one_le_rpow hH1 hδ.le).trans hwidth
  have hG0 : 0 < G := by linarith
  have hl : 1 ≤ Real.log (2*H) :=
    (hD H hDH).trans (Real.log_le_log hH0 (by linarith))
  have hn : (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) ≤ H := by
    have hg := hgeometry H G hAH hwidth
    have hn0 := Nat.cast_nonneg (α := ℝ) (atkinsonSourceCutoff (2*H) G (Real.log (2*H)))
    linarith
  have hn0 := atkinsonSourceCutoff_pos (by positivity : 0 < 2*H) hG0
    (by linarith : 0 < Real.log (2*H))
  have hp := atkinsonPhysical_gap_budget_log_le L R hH1 hG1
    (show 0 ≤ ν/2 by linarith) hn0 hl hn
    (atkinsonPhysicalCutoff_le_natural hH1 hG0 hupper hl)
  have hh : H^(ν/2)*H^(ν/2) = H^ν := by
    rw [← Real.rpow_add hH0]; congr 1; ring
  apply hp.trans
  change C*H^(ν/2)*(Real.log (2*H))^5*_ ≤ _
  calc
    _ ≤ C*H^(ν/2)*H^(ν/2)*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (hB H hBH) (by positivity)
    _ = _ := by rw [mul_assoc C,hh]


end MathCollab.Density.Stronger.Atkinson
