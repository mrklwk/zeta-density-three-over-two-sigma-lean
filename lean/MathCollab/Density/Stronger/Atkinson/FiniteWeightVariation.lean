module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_WEIGHT_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

structure FiniteVariationBound (f : ℕ → ℂ) (N : ℕ) (M : ℝ) : Prop where
  nonneg : 0 ≤ M
  norm_le : ∀ i : ℕ, i ≤ N → ‖f i‖ ≤ M
  variation_le : (∑ i ∈ Finset.range N, ‖f (i+1)-f i‖) ≤ M

theorem FiniteVariationBound.mono {f : ℕ → ℂ} {N : ℕ} {M D : ℝ}
    (hf : FiniteVariationBound f N M) (hMD : M ≤ D) :
    FiniteVariationBound f N D :=
  ⟨hf.nonneg.trans hMD,fun i hi => (hf.norm_le i hi).trans hMD,hf.variation_le.trans hMD⟩

theorem FiniteVariationBound.congr {f g : ℕ → ℂ} {N : ℕ} {M : ℝ}
    (hf : FiniteVariationBound f N M) (he : ∀ i ≤ N, g i = f i) :
    FiniteVariationBound g N M := by
  refine ⟨hf.nonneg,fun i hi => ?_,?_⟩
  · rw [he i hi]
    exact hf.norm_le i hi
  · convert hf.variation_le using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Finset.mem_range.mp hi).le,he (i+1) (Finset.mem_range.mp hi)]

theorem finiteVariationBound_const (c : ℂ) (N : ℕ) :
    FiniteVariationBound (fun _ => c) N ‖c‖ := by
  refine ⟨norm_nonneg _,fun _ _ => le_rfl,?_⟩
  simp only [sub_self,norm_zero,Finset.sum_const_zero,norm_nonneg]

theorem FiniteVariationBound.mul {f g : ℕ → ℂ} {N : ℕ} {M D : ℝ}
    (hf : FiniteVariationBound f N M) (hg : FiniteVariationBound g N D) :
    FiniteVariationBound (fun i => f i*g i) N (2*M*D) := by
  have hMD : 0 ≤ M*D := mul_nonneg hf.nonneg hg.nonneg
  refine ⟨by nlinarith,?_,?_⟩
  · intro i hi
    rw [norm_mul]
    have h := mul_le_mul (hf.norm_le i hi) (hg.norm_le i hi) (norm_nonneg _) hf.nonneg
    nlinarith
  · have hstep (i : ℕ) (hi : i ∈ Finset.range N) :
        ‖f (i+1)*g (i+1)-f i*g i‖ ≤ M*‖g (i+1)-g i‖+D*‖f (i+1)-f i‖ := by
      have hiN : i ≤ N := (Finset.mem_range.mp hi).le
      have hi1N : i+1 ≤ N := Finset.mem_range.mp hi
      rw [show f (i+1)*g (i+1)-f i*g i =
        f (i+1)*(g (i+1)-g i)+(f (i+1)-f i)*g i by ring]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (hf.norm_le _ hi1N) (norm_nonneg _)
      · exact (mul_le_mul_of_nonneg_left (hg.norm_le _ hiN) (norm_nonneg _)).trans_eq (mul_comm _ _)
    apply (Finset.sum_le_sum hstep).trans
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    have h₁ := mul_le_mul_of_nonneg_left hg.variation_le hf.nonneg
    have h₂ := mul_le_mul_of_nonneg_left hf.variation_le hg.nonneg
    nlinarith

theorem finiteVariationBound_of_monotone {u : ℕ → ℝ} {N : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hu : MonotoneOn u (Set.Iic N))
    (hb : ∀ i ≤ N, 0 ≤ u i ∧ u i ≤ M) :
    FiniteVariationBound (fun i => (u i : ℂ)) N M := by
  refine ⟨hM,?_,?_⟩
  · intro i hi
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hb i hi).1] using (hb i hi).2
  · have he : ∑ i ∈ Finset.range N, ‖(u (i+1):ℂ)-(u i:ℂ)‖ = u N-u 0 := by
      calc
        _ = ∑ i ∈ Finset.range N, (u (i+1)-u i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hu (Finset.mem_range.mp hi).le
              (Finset.mem_range.mp hi) (by omega)))]
        _ = _ := Finset.sum_range_sub u N
    rw [he]
    linarith [(hb N le_rfl).2,(hb 0 (Nat.zero_le N)).1]

theorem finiteVariationBound_of_antitone {u : ℕ → ℝ} {N : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hu : AntitoneOn u (Set.Iic N))
    (hb : ∀ i ≤ N, 0 ≤ u i ∧ u i ≤ M) :
    FiniteVariationBound (fun i => (u i : ℂ)) N M := by
  refine ⟨hM,?_,?_⟩
  · intro i hi
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hb i hi).1] using (hb i hi).2
  · have he : ∑ i ∈ Finset.range N, ‖(u (i+1):ℂ)-(u i:ℂ)‖ = u 0-u N := by
      calc
        _ = ∑ i ∈ Finset.range N, (u i-u (i+1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonpos (sub_nonpos.mpr (hu (Finset.mem_range.mp hi).le
              (Finset.mem_range.mp hi) (by omega)))]
          ring
        _ = _ := Finset.sum_range_sub' u N
    rw [he]
    linarith [(hb 0 (Nat.zero_le N)).2,(hb N le_rfl).1]

theorem finiteVariationBound_of_envelope {f : ℕ → ℂ} {e : ℕ → ℝ} {N : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (he : ∀ i ≤ N, 0 ≤ e i) (hm : AntitoneOn e (Set.Iic N))
    (hf : ∀ i ≤ N, ‖f i‖ ≤ M*e i)
    (hd : ∀ i < N, ‖f (i+1)-f i‖ ≤ M*(e i-e (i+1))) :
    FiniteVariationBound f N (M*e 0) := by
  refine ⟨mul_nonneg hM (he 0 (Nat.zero_le N)),?_,?_⟩
  · intro i hi
    exact (hf i hi).trans (mul_le_mul_of_nonneg_left (hm (Nat.zero_le N) hi (Nat.zero_le i)) hM)
  · apply (Finset.sum_le_sum (fun i hi => hd i (Finset.mem_range.mp hi))).trans
    rw [← Finset.mul_sum,Finset.sum_range_sub']
    nlinarith [mul_nonneg hM (he N le_rfl)]

theorem finiteVariationBound_comp_of_lipschitz {f : ℝ → ℂ} {u : ℕ → ℝ}
    {N : ℕ} {a b M : ℝ} (hM : 0 ≤ M) (hab : b-a ≤ 1)
    (hu : MonotoneOn u (Set.Iic N) ∨ AntitoneOn u (Set.Iic N))
    (hr : ∀ i ≤ N, u i ∈ Set.Icc a b)
    (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M)
    (hd : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ‖f y-f x‖ ≤ M*|y-x|) :
    FiniteVariationBound (fun i => f (u i)) N M := by
  refine ⟨hM,fun i hi => hf _ (hr i hi),?_⟩
  have hs : (∑ i ∈ Finset.range N, |u (i+1)-u i|) ≤ 1 := by
    rcases hu with hu | hu
    · have he : ∑ i ∈ Finset.range N, |u (i+1)-u i| = u N-u 0 := by
        calc
          _ = ∑ i ∈ Finset.range N, (u (i+1)-u i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact abs_of_nonneg (sub_nonneg.mpr (hu (Finset.mem_range.mp hi).le
              (Finset.mem_range.mp hi) (by omega)))
          _ = _ := Finset.sum_range_sub u N
      rw [he]
      linarith [(hr N le_rfl).2,(hr 0 (Nat.zero_le N)).1]
    · have he : ∑ i ∈ Finset.range N, |u (i+1)-u i| = u 0-u N := by
        calc
          _ = ∑ i ∈ Finset.range N, (u i-u (i+1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_of_nonpos (sub_nonpos.mpr (hu (Finset.mem_range.mp hi).le
              (Finset.mem_range.mp hi) (by omega)))]
            ring
          _ = _ := Finset.sum_range_sub' u N
      rw [he]
      linarith [(hr 0 (Nat.zero_le N)).2,(hr N le_rfl).1]
  calc
    _ ≤ ∑ i ∈ Finset.range N, M*|u (i+1)-u i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact hd _ (hr i (Finset.mem_range.mp hi).le) _ (hr (i+1) (Finset.mem_range.mp hi))
    _ = M*(∑ i ∈ Finset.range N, |u (i+1)-u i|) := (Finset.mul_sum _ _ _).symm
    _ ≤ M := by nlinarith

theorem norm_sum_mul_le_discrete_parts (w a : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n*a n‖ ≤
      ‖w (N-1)‖*‖∑ n ∈ Finset.range N, a n‖+
        ∑ n ∈ Finset.range (N-1),
          ‖w (n+1)-w n‖*‖∑ k ∈ Finset.range (n+1), a k‖ := by
  have he := Finset.sum_range_by_parts w a N
  simp only [smul_eq_mul] at he
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact add_le_add le_rfl ((norm_sum_le _ _).trans_eq (by simp only [norm_mul]))

theorem FiniteVariationBound.norm_sum_mul_le {w a : ℕ → ℂ} {N : ℕ} {M A : ℝ}
    (hw : FiniteVariationBound w N M) (hA : 0 ≤ A)
    (ha : ∀ j ≤ N, ‖∑ i ∈ Finset.range j, a i‖ ≤ A) :
    ‖∑ i ∈ Finset.range N, w i*a i‖ ≤ 2*M*A := by
  have hv : (∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖) ≤ M := by
    apply le_trans _ hw.variation_le
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N 1))
    intro i _ _
    exact norm_nonneg _
  apply (norm_sum_mul_le_discrete_parts w a N).trans
  have he := mul_le_mul (hw.norm_le (N-1) (Nat.sub_le N 1)) (ha N le_rfl)
    (norm_nonneg _) hw.nonneg
  have hs : (∑ i ∈ Finset.range (N-1),
      ‖w (i+1)-w i‖*‖∑ k ∈ Finset.range (i+1), a k‖) ≤ A*M := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖*A := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left (ha (i+1) (by
          have h := Finset.mem_range.mp hi
          omega)) (norm_nonneg _)
      _ = A*(∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ A*M := mul_le_mul_of_nonneg_left hv hA
  nlinarith

end MathCollab.Density.Stronger.Atkinson
