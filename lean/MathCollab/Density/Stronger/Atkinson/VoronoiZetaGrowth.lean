module
-- Reversible module-visibility port of the audited development.
/-
Native q=1 estimates derived from the existing proved Gamma half-line formula,
beta comparison and actual zeta Abel bound. Existing Gamma/contour Apache
and McColm MIT-0 attributions remain; no Estermann input or assumed source bound.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiZetaFunctional
public import MathCollab.Density.Stronger.PointMean.GammaKernel
public import MathCollab.Density.AbelZetaGrowth

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex
open MathCollab.Density.GammaBounds MathCollab.Density.ZetaGrowth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem norm_Gamma_voronoi_strip_sharp {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤
      12 * (1 + |t|) * Real.exp (-(Real.pi * |t|) / 2) := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [z] at hr
  have hrec : Complex.Gamma (stripPoint (3/2) t) = z * Complex.Gamma z := by
    convert Complex.Gamma_add_one z hz using 1
    congr 1
    dsimp [stripPoint, z]
    push_cast
    ring
  have hn : ‖z‖ ≤ 1 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    norm_num [z] at h
    linarith
  have hhalf := PointMean.norm_Gamma_half_vertical_le_exp t
  have hu : ‖Complex.Gamma (stripPoint (3/2) t)‖ ≤
      (1 + |t|) * (3 * Real.exp (-(Real.pi * |t|) / 2)) := by
    rw [hrec, norm_mul]
    exact mul_le_mul hn hhalf (norm_nonneg _) (by positivity)
  have hs := norm_Gamma_stripPoint_le_four_upper (t := t) ha ha'
  change ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ _ at hs
  calc
    _ ≤ 4 * ‖Complex.Gamma (stripPoint (3/2) t)‖ := hs
    _ ≤ 4 * ((1 + |t|) * (3 * Real.exp (-(Real.pi * |t|) / 2))) := by gcongr
    _ = _ := by ring

theorem norm_complex_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  unfold Complex.cos
  rw [norm_div, norm_ofNat]
  have hp : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have hm : ‖Complex.exp (-(z * I))‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hm' : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by simpa [neg_mul] using hm
  exact (norm_add_le _ _).trans (by linarith)

theorem norm_voronoiFactor_one_le {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 3/2) :
    ‖dfiPeriodicArchimedeanFactor 1 s‖ ≤
      12 * (1 + |s.im|) * Real.exp (-(Real.pi * |s.im|) / 2) := by
  have hbase : ‖(2 * Real.pi : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · nlinarith [Real.pi_gt_three]
    · simpa using (show 0 ≤ s.re by linarith)
  have hG := norm_Gamma_voronoi_strip_sharp (t := s.im) hs hs'
  rw [Complex.re_add_im] at hG
  simpa only [dfiPeriodicArchimedeanFactor, Nat.cast_one, one_cpow, one_mul,
    norm_mul] using (mul_le_of_le_one_left (norm_nonneg (Complex.Gamma s)) hbase).trans hG

theorem norm_voronoiFactor_one_mul_cos_le {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 3/2) :
    ‖dfiPeriodicArchimedeanFactor 1 s * Complex.cos (Real.pi * s / 2)‖ ≤
      12 * (1 + |s.im|) := by
  have hc := norm_complex_cos_le_exp_abs_im (Real.pi * s / 2)
  have him : |(Real.pi * s / 2).im| = Real.pi * |s.im| / 2 := by
    simp only [div_ofNat_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  rw [him] at hc
  rw [norm_mul]
  calc
    _ ≤ (12 * (1 + |s.im|) * Real.exp (-(Real.pi * |s.im|) / 2)) *
        Real.exp (Real.pi * |s.im| / 2) :=
      mul_le_mul (norm_voronoiFactor_one_le hs hs') hc (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add, show -(Real.pi * |s.im|) / 2 + Real.pi * |s.im| / 2 = 0 by ring, Real.exp_zero, mul_one]

theorem norm_riemannZeta_voronoi_strip {σ u : ℝ}
    (hσ : -(1/2 : ℝ) ≤ σ) (hσ' : σ ≤ 3/2) (hu : 1 ≤ |u|) :
    ‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ≤ 240 * (1 + |u|)^2 := by
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hre : z.re = σ := by simp [z]
  have him : z.im = u := by simp [z]
  by_cases hr : 1/2 ≤ σ
  · have hz := norm_riemannZeta_le_five_mul_norm (s := z) (by rw [hre]; linarith)
      (by simpa [him] using hu)
    have hn : ‖z‖ ≤ 2 * (1 + |u|) := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      rw [hre, him, abs_of_nonneg (by linarith : 0 ≤ σ)] at h
      nlinarith [abs_nonneg u]
    change ‖riemannZeta z‖ ≤ _
    nlinarith [sq_nonneg (1 + |u|), abs_nonneg u]
  · have hz0 : z ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      rw [him] at hi
      simp only [zero_im] at hi
      have hu0 : 1 ≤ |(0 : ℝ)| := by simpa only [hi] using hu
      norm_num at hu0
    have hs : 1/2 ≤ (1-z).re := by simp only [sub_re, one_re, hre]; linarith
    have hs' : (1-z).re ≤ 3/2 := by simp only [sub_re, one_re, hre]; linarith
    have hui : |(1-z).im| = |u| := by simp [him]
    have hz := norm_riemannZeta_le_five_mul_norm (s := 1-z) (by linarith)
      (by rw [hui]; exact hu)
    have hn : ‖1-z‖ ≤ 2 * (1 + |u|) := by
      have h := Complex.norm_le_abs_re_add_abs_im (1-z)
      rw [hui, abs_of_nonneg (by linarith : 0 ≤ (1-z).re)] at h
      nlinarith [abs_nonneg u]
    have hc := norm_voronoiFactor_one_mul_cos_le hs hs'
    rw [hui] at hc
    change ‖riemannZeta z‖ ≤ _
    rw [riemannZeta_eq_voronoiFactor (by rw [hre]; linarith) hz0]
    rw [show 2 * dfiPeriodicArchimedeanFactor 1 (1-z) *
      Complex.cos (Real.pi * (1-z) / 2) * riemannZeta (1-z) =
      2 * (dfiPeriodicArchimedeanFactor 1 (1-z) * Complex.cos (Real.pi * (1-z) / 2)) *
        riemannZeta (1-z) by ring]
    rw [norm_mul, norm_mul, norm_ofNat]
    calc
      _ ≤ 2 * (12 * (1 + |u|)) * (10 * (1 + |u|)) := by
        apply mul_le_mul _ (by linarith) (norm_nonneg _) (by positivity)
        gcongr
      _ = _ := by ring

end MathCollab.Density.Stronger.Atkinson
