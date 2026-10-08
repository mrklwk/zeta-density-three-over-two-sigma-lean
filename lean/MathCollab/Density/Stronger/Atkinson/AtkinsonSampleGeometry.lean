module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonSaddle
public import Mathlib.Analysis.Real.Pi.Bounds

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonSaddleRoot_small_frequency {T b : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T / 100) :
    Real.sqrt T / 3 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b ∧
      atkinsonSaddleRoot (T / (2 * Real.pi)) b ≤ Real.sqrt T / 2 := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  let S := Real.sqrt T
  have hS : 0 < S := Real.sqrt_pos.2 hT
  have hSsq : S ^ 2 = T := Real.sq_sqrt hT.le
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hrb : 0 < r - b := atkinsonSaddleRoot_sub_pos (by positivity) b
  have he : r ^ 2 - b * r = T / (2 * Real.pi) := atkinsonSaddleRoot_equation (by positivity) b
  have hAlo : T / 8 ≤ T / (2 * Real.pi) :=
    div_le_div_of_nonneg_left hT.le (by positivity) (by nlinarith [Real.pi_lt_four])
  have hAhi : T / (2 * Real.pi) ≤ T / 6 :=
    div_le_div_of_nonneg_left hT.le (by norm_num) (by nlinarith [Real.pi_gt_three])
  have hbSlo := mul_le_mul_of_nonneg_right (abs_le.mp hb).1 hS.le
  have hbShi := mul_le_mul_of_nonneg_right (abs_le.mp hb).2 hS.le
  change S / 3 ≤ r ∧ r ≤ S / 2
  constructor
  · by_contra hn
    have hprod : (S / 3 - r) * (S / 3 + r - b) > 0 :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · by_contra hn
    have hprod : (r - S / 2) * (r + S / 2 - b) > 0 :=
      mul_pos (by linarith) (by linarith)
    nlinarith

theorem atkinsonSaddleRoot_small_frequency_window {T b H : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T / 100) (hH : H ≤ Real.sqrt T / 12) :
    Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H ∧
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T ∧
        H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 := by
  obtain ⟨hlo, hhi⟩ := atkinsonSaddleRoot_small_frequency hT hb
  constructor
  · linarith
  constructor <;> nlinarith [Real.sqrt_nonneg T]

theorem sqrt_nat_small_frequency {T : ℝ} (hT : 0 < T) (n : ℕ)
    (hn : 10000 * (n : ℝ) ≤ T) : |Real.sqrt (n : ℝ)| ≤ Real.sqrt T / 100 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hTsq := Real.sq_sqrt hT.le
  nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_pos.2 hT]

theorem atkinsonSaddleRoot_inverse_identity {A : ℝ} (hA : 0 < A) (b : ℝ) :
    atkinsonSaddleRoot A b-A/atkinsonSaddleRoot A b = b := by
  have hr := atkinsonSaddleRoot_pos hA b
  have he := atkinsonSaddleRoot_equation hA b
  field_simp
  nlinarith

theorem atkinsonSaddleRoot_monotone {A : ℝ} (hA : 0 < A) :
    Monotone (atkinsonSaddleRoot A) := by
  intro b c hbc
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hdiv := div_le_div_of_nonneg_left hA.le (atkinsonSaddleRoot_pos hA c) hlt.le
  have hb := atkinsonSaddleRoot_inverse_identity hA b
  have hc := atkinsonSaddleRoot_inverse_identity hA c
  linarith

theorem zetaAtkinsonSaddle_monotone {T : ℝ} (hT : 0 < T) :
    Monotone (zetaAtkinsonSaddle T) := by
  intro b c hbc
  exact pow_le_pow_left₀ (atkinsonSaddleRoot_pos (by positivity) b).le
    (atkinsonSaddleRoot_monotone (by positivity) hbc) 2

def atkinsonPositiveRootSample (T : ℝ) (m i : ℕ) : ℝ :=
  atkinsonSaddleRoot (T/(2*Real.pi)) (Real.sqrt ((m+i:ℕ):ℝ)) / Real.sqrt T

def atkinsonNegativeRootSample (T : ℝ) (m i : ℕ) : ℝ :=
  atkinsonSaddleRoot (T/(2*Real.pi)) (-Real.sqrt ((m+i:ℕ):ℝ)) / Real.sqrt T

theorem atkinsonPositiveRootSample_monotone {T : ℝ} (hT : 0 < T) (m : ℕ) :
    Monotone (atkinsonPositiveRootSample T m) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg T)
  apply atkinsonSaddleRoot_monotone (by positivity)
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)

theorem atkinsonNegativeRootSample_antitone {T : ℝ} (hT : 0 < T) (m : ℕ) :
    Antitone (atkinsonNegativeRootSample T m) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg T)
  apply atkinsonSaddleRoot_monotone (by positivity)
  apply neg_le_neg
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)

theorem atkinsonRootSample_mem {T : ℝ} (hT : 0 < T) (m N : ℕ)
    (hN : 10000*((m+N:ℕ):ℝ) ≤ T) (i : ℕ) (hi : i ≤ N) :
    atkinsonPositiveRootSample T m i ∈ Icc (1/4) 1 ∧
      atkinsonNegativeRootSample T m i ∈ Icc (1/4) 1 := by
  have hn : 10000*((m+i:ℕ):ℝ) ≤ T := by
    have hcast : ((m+i:ℕ):ℝ) ≤ (m+N:ℕ) := by exact_mod_cast Nat.add_le_add_left hi m
    linarith
  have hb := sqrt_nat_small_frequency hT (m+i) hn
  have hp := atkinsonSaddleRoot_small_frequency hT hb
  have hm := atkinsonSaddleRoot_small_frequency hT (b := -Real.sqrt ((m+i:ℕ):ℝ))
    (by simpa only [abs_neg] using hb)
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  constructor
  · constructor
    · apply (le_div_iff₀ hs).2
      linarith [hp.1]
    · apply (div_le_iff₀ hs).2
      linarith [hp.2]
  · constructor
    · apply (le_div_iff₀ hs).2
      linarith [hm.1]
    · apply (div_le_iff₀ hs).2
      linarith [hm.2]

end MathCollab.Density.Stronger.Atkinson
