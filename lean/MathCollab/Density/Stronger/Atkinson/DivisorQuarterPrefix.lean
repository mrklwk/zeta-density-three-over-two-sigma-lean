module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_FINITE_ERROR_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.NeumannRemainderSeries

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex Filter
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_divisorDirichletTerm_quarter_le_prefix {ε : ℝ} (hε : 0 < ε)
    {N n : ℕ} (hn : n ≤ N) :
    ‖divisorDirichletTerm (1/4) n‖ ≤ (N:ℝ)^(3/4+ε) *
      ‖divisorDirichletTerm ((1+ε : ℝ) : ℂ) n‖ := by
  by_cases hn0 : n = 0
  · simp [hn0,divisorDirichletTerm,LSeries.term]
  have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hmono : (n:ℝ)^(3/4+ε) ≤ (N:ℝ)^(3/4+ε) :=
    Real.rpow_le_rpow hnR.le (by exact_mod_cast hn) (by positivity)
  have he : (n:ℝ)^(-(1/4 : ℝ)) =
      (n:ℝ)^(3/4+ε) * (n:ℝ)^(-(1+ε)) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hquarter := norm_divisorDirichletTerm_real (1/4) n
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hquarter
  rw [hquarter,norm_divisorDirichletTerm_real,he]
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hnR.le (-(1+ε))))
    (norm_nonneg (divisorWeight n))
  convert h using 1
  ring

theorem exists_sum_norm_divisorDirichletTerm_quarter_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑ n ∈ Finset.range N, ‖divisorDirichletTerm (1/4) n‖) ≤ C*(N:ℝ)^(3/4+ε) := by
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm ((1+ε : ℝ) : ℂ) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  have hs := (summable_divisorDirichletTerm (s := ((1+ε : ℝ) : ℂ))
    (by simpa only [Complex.ofReal_re,lt_add_iff_pos_right] using hε)).norm
  refine ⟨1+S,by positivity,?_⟩
  intro N
  have hprefix : (∑ n ∈ Finset.range N, ‖divisorDirichletTerm ((1+ε : ℝ) : ℂ) n‖) ≤ S :=
    hs.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _)
  calc
    _ ≤ ∑ n ∈ Finset.range N, (N:ℝ)^(3/4+ε) *
        ‖divisorDirichletTerm ((1+ε : ℝ) : ℂ) n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_divisorDirichletTerm_quarter_le_prefix hε (Finset.mem_range.mp hn).le
    _ = (N:ℝ)^(3/4+ε) * ∑ n ∈ Finset.range N,
        ‖divisorDirichletTerm ((1+ε : ℝ) : ℂ) n‖ := by rw [Finset.mul_sum]
    _ ≤ (N:ℝ)^(3/4+ε)*S := mul_le_mul_of_nonneg_left hprefix (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (3/4+ε)]

end MathCollab.Density.Stronger.Atkinson
