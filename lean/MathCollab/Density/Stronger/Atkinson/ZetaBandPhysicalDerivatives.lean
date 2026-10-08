module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_CUTOFF_C2_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Filter Topology
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem exp_gap_lower {r h : ℝ} (hr : -1 ≤ r) (hh : 0 < h) :
    Real.exp (-1) * h ≤ Real.exp (r + h) - Real.exp r := by
  have hm := mul_le_mul (Real.exp_le_exp.mpr hr)
    (show h ≤ Real.exp h - 1 by linarith [Real.add_one_le_exp h]) hh.le (Real.exp_pos r).le
  rw [Real.exp_add]
  convert hm using 1
  ring

theorem zetaDivisorBandEdge_normalized_gap_lower {G L : ℝ}
    (hG : 0 < G) (hL : 0 < L) (v : ℝ) (hv : -1 ≤ v / G) :
    Real.exp (-1) * (L / G) / (2 * Real.pi) ≤
      zetaDivisorBandEdge 1 G (v + L) - zetaDivisorBandEdge 1 G v := by
  have h := div_le_div_of_nonneg_right
    (exp_gap_lower hv (div_pos hL hG)) (by positivity : 0 ≤ 2 * Real.pi)
  unfold zetaDivisorBandEdge
  rw [add_div]
  convert h using 1
  ring

theorem zetaDivisorBandCutoff_inverse_widths {G L : ℝ}
    (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    1 / (zetaDivisorBandEdge 1 G (-L) - zetaDivisorBandEdge 1 G (-2 * L)) ≤
        2 * Real.pi * Real.exp 1 * G / L ∧
    1 / (zetaDivisorBandEdge 1 G (2 * L) - zetaDivisorBandEdge 1 G L) ≤
        2 * Real.pi * Real.exp 1 * G / L := by
  have hinv (D : ℝ) (hD : Real.exp (-1) * (L / G) / (2 * Real.pi) ≤ D) :
      1 / D ≤ 2 * Real.pi * Real.exp 1 * G / L := by
    have hbase : 0 < Real.exp (-1) * (L / G) / (2 * Real.pi) := by positivity
    apply (div_le_iff₀ (hbase.trans_le hD)).2
    have h := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ 2 * Real.pi * Real.exp 1 * G / L by positivity)
    have he : (2 * Real.pi * Real.exp 1 * G / L) *
        (Real.exp (-1) * (L / G) / (2 * Real.pi)) = 1 := by
      rw [Real.exp_neg]
      field_simp
    rw [he] at h
    exact h
  constructor
  · apply hinv
    have h := zetaDivisorBandEdge_normalized_gap_lower hG hL (-2 * L)
      ((le_div_iff₀ hG).2 (by linarith))
    simpa only [show -2 * L + L = -L by ring] using h
  · apply hinv
    have h := zetaDivisorBandEdge_normalized_gap_lower hG hL L
      ((le_div_iff₀ hG).2 (by linarith))
    simpa only [show L + L = 2 * L by ring] using h

theorem zetaBandCutoff_mul_height {T : ℝ} (hT : T ≠ 0) (a b c d x : ℝ) :
    zetaBandCutoff (T * a) (T * b) (T * c) (T * d) (T * x) =
      zetaBandCutoff a b c d x := by
  unfold zetaBandCutoff
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hT,
    ← mul_sub, ← mul_sub, mul_div_mul_left _ _ hT]

theorem zetaDivisorBandCutoff_root_rescale {T : ℝ} (hT : T ≠ 0) (G L u : ℝ) :
    zetaDivisorBandCutoff T G L (T * u ^ 2) = zetaDivisorBandCutoff 1 G L (u ^ 2) := by
  have he (v : ℝ) : zetaDivisorBandEdge T G v = T * zetaDivisorBandEdge 1 G v := by
    unfold zetaDivisorBandEdge
    ring
  simp only [zetaDivisorBandCutoff, he]
  exact zetaBandCutoff_mul_height hT _ _ _ _ _

theorem exists_intervalC2Bound_zetaDivisorBandCutoff_root :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → 1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (fun u => (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ))
        (1 / 4) 1 C ((1 + 2 * Real.pi * Real.exp 1) * G) := by
  obtain ⟨M, hM, hquad⟩ := exists_intervalC2Bound_quadraticTransition
  refine ⟨4 * M * M, by positivity, ?_⟩
  intro T G L hT hG hL hwidth
  let a := zetaDivisorBandEdge 1 G (-2 * L)
  let b := zetaDivisorBandEdge 1 G (-L)
  let c := zetaDivisorBandEdge 1 G L
  let d := zetaDivisorBandEdge 1 G (2 * L)
  let R := (1 + 2 * Real.pi * Real.exp 1) * G
  have hL0 : 0 < L := by linarith
  have hm := zetaDivisorBandEdge_strictMono (by norm_num : (0 : ℝ) < 1) hG
  have hab : a < b := hm (by linarith)
  have hcd : c < d := hm (by linarith)
  have hR : 1 ≤ R := by
    dsimp [R]
    have hp : 0 < 2 * Real.pi * Real.exp 1 := by positivity
    nlinarith
  have hinv := zetaDivisorBandCutoff_inverse_widths hG hL0 hwidth
  have hbound : 2 * Real.pi * Real.exp 1 * G / L ≤ R := by
    apply (div_le_self (by positivity) hL).trans
    dsimp [R]
    nlinarith
  have hleft : |1 / (b - a)| ≤ R := by
    rw [abs_of_pos (by positivity : 0 < 1 / (b - a))]
    exact hinv.1.trans hbound
  have hright : |-(1 / (d - c))| ≤ R := by
    rw [abs_neg, abs_of_pos (by positivity : 0 < 1 / (d - c))]
    exact hinv.2.trans hbound
  have hf := hquad (1 / (b - a)) (-a / (b - a)) R hR hleft
  have hg := hquad (-(1 / (d - c))) (d / (d - c)) R hR hright
  have he : (fun u => (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ)) =
      fun u => (Real.smoothTransition ((1 / (b - a)) * u ^ 2 + -a / (b - a)) : ℂ) *
        (Real.smoothTransition ((-(1 / (d - c))) * u ^ 2 + d / (d - c)) : ℂ) := by
    funext u
    rw [zetaDivisorBandCutoff_root_rescale hT.ne']
    change (zetaBandCutoff a b c d (u ^ 2) : ℂ) = _
    simp only [zetaBandCutoff, Complex.ofReal_mul]
    have hl : (u ^ 2 - a) / (b - a) = (1 / (b - a)) * u ^ 2 + -a / (b - a) := by ring
    have hr : (d - u ^ 2) / (d - c) = (-(1 / (d - c))) * u ^ 2 + d / (d - c) := by ring
    rw [hl, hr]
  rw [he]
  exact hf.mul hg

end MathCollab.Density.Stronger.Atkinson
