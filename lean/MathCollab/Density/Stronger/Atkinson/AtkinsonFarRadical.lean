module
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFarCurvature

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

/-!
# Radical simplification of the far-gap B-process

The moderate-gap branch uses the actual curvature scales. Above Q=M*R,
the triangle bound M is stronger. This keeps the square-root growth
without imposing an artificial upper bound on the height gap.
-/

set_option autoImplicit false
noncomputable section

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinson_far_inverse_sqrt {Q d lam : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) (hlam : d/(320*Q) ≤ lam) :
    1/Real.sqrt lam ≤ 20*Real.sqrt (Q/d) := by
  have hi := one_div_le_one_div_of_le (by positivity : 0 < d/(320*Q)) hlam
  have hi' : 1/lam ≤ 400*(Q/d) := by
    have h := hi.trans_eq (by rw [one_div_div])
    have h' : 1/lam ≤ 320*(Q/d) := h.trans_eq (by ring)
    nlinarith [div_pos hQ hd]
  calc
    _ = Real.sqrt (1/lam) := by rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
    _ ≤ Real.sqrt (400*(Q/d)) := Real.sqrt_le_sqrt hi'
    _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num

theorem atkinson_far_second_factor {Q d lam : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) (hdQ : d ≤ Q) (hlam : d/(320*Q) ≤ lam) :
    2*Real.pi/Real.sqrt lam+2*(Real.sqrt lam/lam+1) ≤
      202*Real.sqrt (Q/d) := by
  have hi := atkinson_far_inverse_sqrt hQ hd hlam
  have hy : 1 ≤ Real.sqrt (Q/d) :=
    Real.one_le_sqrt.mpr ((le_div_iff₀ hd).mpr (by simpa using hdQ))
  have hc : 2*Real.pi+2 ≤ 10 := by linarith [Real.pi_lt_four]
  have hm := mul_le_mul hc hi (by positivity : 0 ≤ 1/Real.sqrt lam) (by norm_num : (0:ℝ) ≤ 10)
  calc
    _ = (2*Real.pi+2)*(1/Real.sqrt lam)+2 := by rw [Real.sqrt_div_self']; ring
    _ ≤ 10*(20*Real.sqrt (Q/d))+2 := by linarith
    _ ≤ _ := by linarith

theorem atkinson_far_radical_identity {M R d : ℝ}
    (hR : 0 < R) (hd : 0 < d) :
    (d/R)*Real.sqrt (M*R/d) = Real.sqrt (M*d/R) := by
  calc
    _ = Real.sqrt ((d/R)^2)*Real.sqrt (M*R/d) := by rw [Real.sqrt_sq (div_pos hd hR).le]
    _ = Real.sqrt ((d/R)^2*(M*R/d)) := (Real.sqrt_mul (sq_nonneg _) _).symm
    _ = _ := by congr 1; field_simp

theorem atkinson_far_min_bProcess {M R d lam upper : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hRd : R ≤ d)
    (hlam : d/(320*(M*R)) ≤ lam) (hupper0 : 0 ≤ upper)
    (hupper : upper ≤ 4*d/(M*R)) :
    min M ((M*upper/(2*Real.pi)+2)*
      (2*Real.pi/Real.sqrt lam+2*(Real.sqrt lam/lam+1))) ≤
      2000*Real.sqrt (M*d/R) := by
  have hd : 0 < d := hR.trans_le hRd
  have hQ : 0 < M*R := mul_pos hM hR
  have hlam0 : 0 < lam := (div_pos hd (by positivity : 0 < 320*(M*R))).trans_le hlam
  by_cases hdQ : d ≤ M*R
  · have hsecond := atkinson_far_second_factor hQ hd hdQ hlam
    have hdiv := div_le_self (mul_nonneg hM.le hupper0)
      (show (1:ℝ) ≤ 2*Real.pi by linarith [Real.pi_gt_three])
    have hmul := mul_le_mul_of_nonneg_left hupper hM.le
    have hmul' : M*upper ≤ 4*(d/R) := hmul.trans_eq (by field_simp)
    have hr : 1 ≤ d/R := (le_div_iff₀ hR).mpr (by simpa using hRd)
    have hfirst : M*upper/(2*Real.pi)+2 ≤ 6*(d/R) := by linarith
    have hprod := mul_le_mul hfirst hsecond (by positivity)
      (by positivity : 0 ≤ 6*(d/R))
    apply (min_le_right _ _).trans
    calc
      _ ≤ (6*(d/R))*(202*Real.sqrt (M*R/d)) := hprod
      _ = 1212*((d/R)*Real.sqrt (M*R/d)) := by ring
      _ = 1212*Real.sqrt (M*d/R) := by rw [atkinson_far_radical_identity hR hd]
      _ ≤ _ := by nlinarith [Real.sqrt_nonneg (M*d/R)]
  · have hMd : M*R ≤ d := le_of_not_ge hdQ
    have hroot : M ≤ Real.sqrt (M*d/R) := by
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ hR]
      nlinarith [mul_le_mul_of_nonneg_left hMd hM.le]
    exact (min_le_left _ _).trans (hroot.trans (by nlinarith [Real.sqrt_nonneg (M*d/R)]))

end MathCollab.Density.Stronger.Atkinson
