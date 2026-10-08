module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected proof slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow stationary refinement; see third_party/twelfth/ATKINSON_SYMMETRIC_MANIFEST.json.
Mathlib and previously ported PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalStationary

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Odd terms and quantitative symmetric stationary remainders

The actual amplitude has a quadratic remainder after its linear term.
The true logarithmic phase has a quartic remainder after its cubic term.
These are pointwise estimates; subsequent integration must prove that
the two odd terms vanish, rather than discard them by assertion.
-/

noncomputable section

open Complex Set

namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC2Bound.norm_deriv_sub_le {f : ℝ → ℂ} {a b M R x y : ℝ}
    (hf : IntervalC2Bound f a b M R) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖deriv f y - deriv f x‖ ≤ M * R ^ 2 * |y - x| := by
  have hd (z : ℝ) (hz : z ∈ Icc a b) : DifferentiableAt ℝ (deriv f) z :=
    ((hf.smooth z hz).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hb (z : ℝ) (hz : z ∈ Icc a b) : ‖deriv (deriv f) z‖ ≤ M * R ^ 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hf.second_le z hz
  simpa only [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hd hb hx hy

theorem IntervalC2Bound.norm_sub_linear_le {f : ℝ → ℂ} {a b M R r H y : ℝ}
    (hf : IntervalC2Bound f a b M R) (hH : 0 ≤ H)
    (hleft : a ≤ r - H) (hright : r + H ≤ b) (hy : |y - r| ≤ H) :
    ‖f y - f r - ((y - r : ℝ) : ℂ) * deriv f r‖ ≤ M * R ^ 2 * H ^ 2 := by
  have hmem {z : ℝ} (hz : z ∈ Icc (r - H) (r + H)) : z ∈ Icc a b :=
    ⟨hleft.trans hz.1, hz.2.trans hright⟩
  have hr : r ∈ Icc (r - H) (r + H) := ⟨by linarith, by linarith⟩
  have hym : y ∈ Icc (r - H) (r + H) := by
    constructor <;> linarith [(abs_le.mp hy).1, (abs_le.mp hy).2]
  let F : ℝ → ℂ := fun z => f z - ((z - r : ℝ) : ℂ) * deriv f r
  have hF (z : ℝ) (hz : z ∈ Icc (r - H) (r + H)) :
      HasDerivAt F (deriv f z - deriv f r) z := by
    have h := (((hasDerivAt_id z).sub_const r).ofReal_comp.mul_const (deriv f r))
    simpa only [F, Complex.ofReal_one, one_mul] using!
      ((hf.smooth z (hmem hz)).differentiableAt (by norm_num)).hasDerivAt.sub h
  have hbound (z : ℝ) (hz : z ∈ Icc (r - H) (r + H)) :
      ‖deriv F z‖ ≤ M * R ^ 2 * H := by
    rw [(hF z hz).deriv]
    apply (hf.norm_deriv_sub_le (hmem hr) (hmem hz)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.nonneg (sq_nonneg R))
    exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have h := (convex_Icc (r - H) (r + H)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hF z hz).differentiableAt) hbound hr hym
  have he : F y - F r = f y - f r - ((y - r : ℝ) : ℂ) * deriv f r := by
    simp only [F, sub_self, Complex.ofReal_zero, zero_mul, sub_zero]
    ring
  rw [he, Real.norm_eq_abs] at h
  apply h.trans
  calc
    _ ≤ M * R ^ 2 * H * H := mul_le_mul_of_nonneg_left hy
      (mul_nonneg (mul_nonneg hf.nonneg (sq_nonneg R)) hH)
    _ = _ := by ring

theorem norm_exp_real_phase_sub_linear_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * I) - 1 - (x : ℂ) * I‖ ≤ 3 * x ^ 2 := by
  have hxnorm : ‖(x : ℂ) * I‖ = |x| := by simp [Real.norm_eq_abs]
  by_cases hx : |x| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := (x : ℂ) * I) (by rwa [hxnorm])
    rw [hxnorm, sq_abs] at h
    nlinarith [sq_nonneg x]
  · have hnorm : ‖Complex.exp ((x : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp]
    have h := (norm_sub_le (Complex.exp ((x : ℂ) * I) - 1) ((x : ℂ) * I)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    rw [hnorm, norm_one, hxnorm] at h
    have hx1 : 1 < |x| := lt_of_not_ge hx
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - 1)]

theorem abs_log_one_add_sub_cubic_le {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) - z + z ^ 2 / 2 - z ^ 3 / 3| ≤ 2 * |z| ^ 4 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -z)
    (by rw [abs_neg]; linarith) 3
  norm_num [Finset.sum_range_succ] at h
  have he : -z + z ^ 2 / 2 + (-z) ^ 3 / 3 + Real.log (1 + z) =
      Real.log (1 + z) - z + z ^ 2 / 2 - z ^ 3 / 3 := by ring
  rw [he] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - |z|)).2
  have hp : 0 ≤ |z| ^ 4 := by positivity
  nlinarith

def atkinsonRootCubicCorrection (T b y : ℝ) : ℝ :=
  (2 * T / 3) * ((y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
    atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3

theorem abs_atkinsonRootPhase_sub_cubic_le {T y : ℝ} (hT : 0 < T) (b : ℝ)
    (hy : |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ≤
      atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    |2 * Real.pi * (atkinsonRootPhase T b y - atkinsonRootQuadratic T b y) -
      atkinsonRootCubicCorrection T b y| ≤
      4 * T * |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ^ 4 /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 4 := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hy0 : 0 < y := by change |y-r| ≤ r/2 at hy; linarith [(abs_le.mp hy).1]
  have hz : |(y-r)/r| ≤ 1/2 := by
    rw [abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hr).2
    change |y-r| ≤ r/2 at hy
    linarith
  rw [atkinsonRootPhase_sub_quadratic hT hy0 b]
  change |2 * Real.pi * ((T / Real.pi) *
    (Real.log (1+(y-r)/r) - (y-r)/r + ((y-r)/r)^2/2)) -
      (2*T/3)*((y-r)/r)^3| ≤ _
  have he : 2 * Real.pi * ((T / Real.pi) *
      (Real.log (1+(y-r)/r) - (y-r)/r + ((y-r)/r)^2/2)) -
        (2*T/3)*((y-r)/r)^3 =
      2*T*(Real.log (1+(y-r)/r) - (y-r)/r + ((y-r)/r)^2/2 - ((y-r)/r)^3/3) := by
    field_simp
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2*T)]
  apply (mul_le_mul_of_nonneg_left (abs_log_one_add_sub_cubic_le hz) (by positivity)).trans_eq
  rw [abs_div, abs_of_pos hr]
  ring

theorem norm_atkinsonRootKernel_sub_cubic_le {T y : ℝ} (hT : 0 < T) (b : ℝ)
    (hy : |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ≤
      atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    ‖atkinsonRootKernel T b y - atkinsonRootQuadraticKernel T b y *
      (1 + (atkinsonRootCubicCorrection T b y : ℂ) * I)‖ ≤
      4*T*|y-atkinsonSaddleRoot (T/(2*Real.pi)) b|^4 /
        (atkinsonSaddleRoot (T/(2*Real.pi)) b)^4 +
      4*T^2*|y-atkinsonSaddleRoot (T/(2*Real.pi)) b|^6 /
        (atkinsonSaddleRoot (T/(2*Real.pi)) b)^6 := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  let q := 2 * Real.pi * atkinsonRootQuadratic T b y
  let d := atkinsonRootCubicCorrection T b y
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have he : atkinsonRootQuadraticKernel T b y * Complex.exp ((d : ℂ) * I) =
      Complex.exp (((q+d : ℝ) : ℂ) * I) := by
    rw [atkinsonRootQuadraticKernel, ← Complex.exp_add]
    congr 1
    dsimp [q]
    push_cast
    ring
  have ha : atkinsonRootKernel T b y =
      Complex.exp (((2*Real.pi*atkinsonRootPhase T b y : ℝ) : ℂ) * I) := by
    unfold atkinsonRootKernel
    congr 1
    push_cast
    ring
  have hfirst : ‖atkinsonRootKernel T b y -
      atkinsonRootQuadraticKernel T b y * Complex.exp ((d : ℂ)*I)‖ ≤
        4*T*|y-r|^4/r^4 := by
    rw [he, ha]
    apply (norm_exp_real_phase_sub_le _ _).trans
    convert abs_atkinsonRootPhase_sub_cubic_le hT b hy using 1
    congr 1
    dsimp [q,d]
    ring
  have hsecond : ‖atkinsonRootQuadraticKernel T b y * Complex.exp ((d : ℂ)*I) -
      atkinsonRootQuadraticKernel T b y * (1+(d : ℂ)*I)‖ ≤
        4*T^2*|y-r|^6/r^6 := by
    rw [← mul_sub, norm_mul, norm_atkinsonRootQuadraticKernel, one_mul,
      show Complex.exp ((d : ℂ)*I) - (1+(d : ℂ)*I) =
        Complex.exp ((d : ℂ)*I)-1-(d : ℂ)*I by ring]
    apply (norm_exp_real_phase_sub_linear_le d).trans
    have hd : d^2 = (4*T^2/9)*|y-r|^6/r^6 := by
      dsimp [d, atkinsonRootCubicCorrection]
      rw [show |y-r|^6 = (y-r)^6 by
        calc
          _ = (|y-r|^2)^3 := by ring
          _ = ((y-r)^2)^3 := by rw [sq_abs]
          _ = _ := by ring]
      ring
    rw [hd]
    have hp : 0 ≤ T^2*|y-r|^6/r^6 := by positivity
    calc
      _ = (4/3 : ℝ) * (T^2*|y-r|^6/r^6) := by ring
      _ ≤ 4 * (T^2*|y-r|^6/r^6) := mul_le_mul_of_nonneg_right (by norm_num) hp
      _ = _ := by ring
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hsecond)

end MathCollab.Density.Stronger.Atkinson
