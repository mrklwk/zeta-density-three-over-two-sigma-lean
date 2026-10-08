module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixGapBound
public import WeylPort.GrowthAlgebra
public import Mathlib.Data.Nat.Log

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Filter
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSourceCutoff (T G L : ℝ) : ℕ := ⌈36 * T * (L / G) ^ 2⌉₊

theorem atkinsonSourceCutoff_lower (T G L : ℝ) :
    36 * T * (L / G) ^ 2 ≤ (atkinsonSourceCutoff T G L : ℝ) :=
  Nat.le_ceil _

theorem atkinsonSourceCutoff_pos {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) : 0 < atkinsonSourceCutoff T G L := by
  have h := (by positivity : 0 < 36 * T * (L / G) ^ 2).trans_le
    (atkinsonSourceCutoff_lower T G L)
  exact_mod_cast h

theorem atkinsonSourceCutoff_le_small {T G L : ℝ}
    (hT : 40000 ≤ T) (hG : 0 < G) (hL : 0 ≤ L) (hwidth : 1200 * L ≤ G) :
    10000 * (atkinsonSourceCutoff T G L : ℝ) ≤ T := by
  have hT0 : 0 < T := by linarith
  have hratio : L / G ≤ 1 / 1200 := (div_le_iff₀ hG).2 (by linarith)
  have hband : 36 * T * (L / G) ^ 2 ≤ T / 40000 := by
    calc
      _ ≤ 36 * T * (1 / 1200 : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 36 * T * (L / G) ^ 2)
  change (atkinsonSourceCutoff T G L : ℝ) < 36 * T * (L / G) ^ 2 + 1 at hceil
  linarith


theorem eventually_atkinsonSourceCutoff_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G →
      10000 * (atkinsonSourceCutoff T G (Real.log T) : ℝ) ≤ T := by
  filter_upwards [TaoTrudgianYang2025.eventually_const_log_pow_le_rpow 1200 (by norm_num) 1 hδ,
    eventually_ge_atTop (40000 : ℝ)] with T hlog hT
  intro G hG
  have hG0 : 0 < G := (Real.rpow_pos_of_pos (by linarith : 0 < T) δ).trans_le hG
  apply atkinsonSourceCutoff_le_small hT hG0 (Real.log_nonneg (by linarith))
  simpa only [pow_one] using hlog.trans hG


def atkinsonPacketCutoff (G : ℝ) (W : Finset ℝ) : ℕ :=
  W.sup (fun t => atkinsonSourceCutoff t G (Real.log t))

theorem atkinsonSourceCutoff_le_packet (G : ℝ) {W : Finset ℝ} {t : ℝ} (ht : t ∈ W) :
    atkinsonSourceCutoff t G (Real.log t) ≤ atkinsonPacketCutoff G W := by
  unfold atkinsonPacketCutoff
  exact Finset.le_sup (f := fun t : ℝ => atkinsonSourceCutoff t G (Real.log t)) ht


theorem atkinsonSourceCutoff_log_mono_height {t u G : ℝ}
    (ht : 1 ≤ t) (htu : t ≤ u) (hG : 0 < G) :
    atkinsonSourceCutoff t G (Real.log t) ≤ atkinsonSourceCutoff u G (Real.log u) := by
  apply Nat.ceil_mono
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := ht0.trans_le htu
  have hlog : Real.log t ≤ Real.log u := Real.log_le_log ht0 htu
  have hratio := div_le_div_of_nonneg_right hlog hG.le
  have hs := pow_le_pow_left₀ (div_nonneg (Real.log_nonneg ht) hG.le) hratio 2
  exact mul_le_mul (mul_le_mul_of_nonneg_left htu (by norm_num)) hs
    (sq_nonneg _) (by positivity)

theorem atkinsonPacketCutoff_le_height {H G : ℝ} {W : Finset ℝ}
    (hH : 1 ≤ H) (hG : 0 < G) (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) :
    atkinsonPacketCutoff G W ≤ atkinsonSourceCutoff (2*H) G (Real.log (2*H)) := by
  unfold atkinsonPacketCutoff
  apply Finset.sup_le
  intro t ht
  exact atkinsonSourceCutoff_log_mono_height (hH.trans (hrange t ht).1) (hrange t ht).2 hG


theorem atkinson_doubled_height_half_power {H δ : ℝ} (hH : 2 ≤ H) (hδ : 0 < δ) :
    (2*H)^(δ/2) ≤ H^δ := by
  have hH0 : 0 < H := by linarith
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH0.le]
  calc
    (2:ℝ)^(δ/2)*H^(δ/2) ≤ H^(δ/2)*H^(δ/2) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by norm_num) hH (by linarith)) (Real.rpow_nonneg hH0.le _)
    _ = H^δ := by rw [← Real.rpow_add hH0]; congr 1; ring

theorem exists_atkinsonPhysicalCutoff_prefix_geometry {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      2*(atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ)+2 ≤ H := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp
    (eventually_atkinsonSourceCutoff_small (show 0 < δ/2 by linarith))
  refine ⟨max 40000 A,le_max_left _ _,?_⟩
  intro H G hH hG
  have hlarge : 40000 ≤ H := (le_max_left _ _).trans hH
  have hAH : A ≤ H := (le_max_right _ _).trans hH
  have hwidth := (atkinson_doubled_height_half_power (by linarith : 2 ≤ H) hδ).trans hG
  have hcut := hA (2*H) (by linarith) G hwidth
  linarith

theorem atkinson_dyadic_prefix_geometry {H G : ℝ} {j : ℕ}
    (hcut : 2*(atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ)+2 ≤ H)
    (hj : j < Nat.clog 2 (atkinsonSourceCutoff (2*H) G (Real.log (2*H)))) :
    (((2^j)+(2^j)+2:ℕ):ℝ) ≤ H := by
  have hjN := Nat.pow_lt_of_lt_clog hj
  have hcast : (((2^j):ℕ):ℝ) ≤
      (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) := by exact_mod_cast hjN.le
  push_cast at hcast ⊢
  linarith

theorem exists_atkinsonPhysicalPrefixGramMax_le_gap {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      ∀ j : ℕ, j < Nat.clog 2 (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) →
      ∀ t u : ℝ, H ≤ t → t ≤ 2*H → H ≤ u → u ≤ 2*H →
        atkinsonPrefixGramMax (2^j) (2^j) t u ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u := by
  obtain ⟨A,hA,hcut⟩ := exists_atkinsonPhysicalCutoff_prefix_geometry hδ
  refine ⟨A,hA,?_⟩
  intro H G hH hG j hj t u ht htU hu huU
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hend := atkinson_dyadic_prefix_geometry (hcut H G hH hG) hj
  exact atkinsonPrefixGramMax_le_gap (lt_min (hH0.trans_le ht) (hH0.trans_le hu))
    (pow_pos (by norm_num) _) (le_min (hend.trans ht) (hend.trans hu))
    (max_le (by linarith [le_min ht hu]) (by linarith [le_min ht hu]))


end MathCollab.Density.Stronger.Atkinson
