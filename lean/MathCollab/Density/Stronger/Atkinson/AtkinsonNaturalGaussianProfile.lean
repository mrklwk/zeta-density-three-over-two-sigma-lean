module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaGaussianNaturalDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootLogProfile

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex Set Filter
open scoped ContDiff Topology
namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC2Bound.comp_div {f : ℝ → ℂ} {a b M R c : ℝ}
    (hf : IntervalC2Bound f a b M R) (hc : 0 < c) :
    IntervalC2Bound (fun y => f (y / c)) (c * a) (c * b) M (R / c) := by
  have hmem {y : ℝ} (hy : y ∈ Icc (c * a) (c * b)) : y / c ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hc).2; nlinarith [hy.1]
    · apply (div_le_iff₀ hc).2; nlinarith [hy.2]
  have hg : ContDiff ℝ 2 (fun y : ℝ => y / c) := by fun_prop
  have hderiv : deriv (fun y : ℝ => y / c) = fun _ => 1 / c := by
    funext y
    exact ((hasDerivAt_id y).div_const c).deriv
  have hsecond (y : ℝ) : iteratedDeriv 2 (fun z : ℝ => z / c) y = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv, deriv_const]
  refine ⟨hf.nonneg, div_nonneg hf.scale_nonneg hc.le,
    fun y hy => (hf.smooth (y / c) (hmem hy)).comp y hg.contDiffAt,
    fun y hy => hf.norm_le (y / c) (hmem hy), ?_, ?_⟩
  · intro y hy
    have hd : HasDerivAt (fun z => f (z / c)) ((1 / c : ℝ) • deriv f (y / c)) y :=
      ((hf.smooth (y / c) (hmem hy)).differentiableAt (by norm_num)).hasDerivAt.scomp
        y ((hasDerivAt_id y).div_const c)
    rw [hd.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / c)]
    apply (mul_le_mul_of_nonneg_left (hf.deriv_le (y / c) (hmem hy)) (by positivity)).trans_eq
    ring
  · intro y hy
    rw [iteratedDeriv_two_comp_real (g := fun z => z / c)
      (hf.smooth (y / c) (hmem hy)) hg.contDiffAt,
      hderiv, hsecond, zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
    apply (mul_le_mul_of_nonneg_left (hf.second_le (y / c) (hmem hy)) (sq_nonneg (1 / c))).trans_eq
    ring

theorem exists_intervalC2Bound_zetaQuadraticLogGaussian_root_natural :
    ∃ C : ℝ, 0 < C ∧ ∀ T G : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      IntervalC2Bound (fun u => zetaGaussianQuadraticIntegral T G
        (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi)))) (1 / 4) 1 (C * G) G := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_quadraticGaussian_profile_natural
    (v := atkinsonRootLogProfile) (a := 1 / 4) (b := 1) (by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      unfold atkinsonRootLogProfile
      fun_prop (disch := exact hu0.ne'))
  refine ⟨C, hC, ?_⟩
  intro T G hT hG hGT
  apply (hbound T G hT hG hGT).congr_of_eventuallyEq
  intro u hu
  filter_upwards [Ioi_mem_nhds (show 0 < u by linarith [hu.1])] with y hy
  exact (zetaQuadraticLogGaussian_root_rescale hT hy G).symm


end MathCollab.Density.Stronger.Atkinson
