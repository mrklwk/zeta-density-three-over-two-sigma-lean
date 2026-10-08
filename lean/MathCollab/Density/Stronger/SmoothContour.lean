module
-- Reversible module-visibility port of the audited development.
/-
The finite rectangle argument adapts the local DetectorContour proof,
itself adapted from McColm TypeIICoverage at exact pin
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. The imported rectangle
residue machinery retains its upstream Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.MellinEntire
public import MathCollab.Density.DetectorContour

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory Set Filter
open MathCollab.Density.ZetaGrowth MathCollab.Density.Contour
open scoped BigOperators Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

def smoothDetectorKernel (ψ : ℝ → ℝ) (ρ : ℂ) (X N q : ℝ) (s : ℂ) : ℂ :=
  (N : ℂ)^s * mellin (fun y => (dampedCutoff ψ q y : ℂ)) s *
    zetaMollifier X (ρ+s) * riemannZeta (ρ+s)

def smoothContourNumerator (ψ : ℝ → ℝ) (ρ : ℂ) (X N q : ℝ) (s : ℂ) : ℂ :=
  (N : ℂ)^s * mellin (fun y => (dampedCutoff ψ q y : ℂ)) s *
    zetaMollifier X (ρ+s) * shiftedRegularizedZeta ρ s

def smoothDetectorResidue (ψ : ℝ → ℝ) (ρ : ℂ) (X N q : ℝ) : ℂ :=
  (N : ℂ)^(1-ρ) * mellin (fun y => (dampedCutoff ψ q y : ℂ)) (1-ρ) *
    zetaMollifier X 1

theorem smoothContourNumerator_div_eq_kernel (ψ : ℝ → ℝ) (ρ : ℂ) (X N q : ℝ)
    {s : ℂ} (hs : s ≠ 1-ρ) :
    smoothContourNumerator ψ ρ X N q s / (s-(1-ρ)) =
      smoothDetectorKernel ψ ρ X N q s := by
  have hp : ρ+s ≠ 1 := by intro h; apply hs; linear_combination h
  unfold smoothContourNumerator smoothDetectorKernel
  rw [shiftedRegularizedZeta_eq hp]
  field_simp [sub_ne_zero.mpr hs]

theorem smoothContourNumerator_at_pole (ψ : ℝ → ℝ) (ρ : ℂ) (X N q : ℝ) :
    smoothContourNumerator ψ ρ X N q (1-ρ) = smoothDetectorResidue ψ ρ X N q := by
  have hp : ρ+(1-ρ) = 1 := by ring
  simp [smoothContourNumerator, smoothDetectorResidue, shiftedRegularizedZeta,
    hp, regularizedRiemannZeta]

theorem smoothContourNumerator_differentiable {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hs : tsupport ψ ⊆ Icc a b)
    (ρ : ℂ) (X q : ℝ) {N : ℝ} (hN : 0 < N) :
    Differentiable ℂ (smoothContourNumerator ψ ρ X N q) := by
  intro s
  have hBase : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hPow : DifferentiableAt ℂ (fun z : ℂ => (N : ℂ)^z) s :=
    differentiableAt_id.const_cpow (Or.inl hBase)
  have hMellin := (dampedCutoff_mellin_entire hψ ha hs q s (mem_univ s)).differentiableAt
  have hMollifier : DifferentiableAt ℂ (fun z : ℂ => zetaMollifier X (ρ+z)) s :=
    (differentiableAt_zetaMollifier X (ρ+s)).comp s
      ((differentiableAt_const (𝕜 := ℂ) ρ).add differentiableAt_id)
  exact ((hPow.mul hMellin).mul hMollifier).mul
    (differentiableAt_shiftedRegularizedZeta ρ s)

/-- The simple-pole residue formula for an entire numerator. -/
theorem entire_div_sub_rectangle {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {z w p : ℂ} (hzRe : z.re ≤ w.re) (hzIm : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => F s/(s-p)) z w = F p := by
  have hg : HolomorphicOn (dslope F p) (Rectangle z w) :=
    (Complex.differentiableOn_dslope hp).2 hF.differentiableOn
  apply ResidueTheoremOnRectangleWithSimplePole hzRe hzIm hp hg
  intro s hs
  have hsp : s ≠ p := by simpa using hs.2
  change F s/(s-p) - F p/(s-p) = dslope F p s
  rw [← sub_div, ← sub_smul_dslope F p s, smul_eq_mul,
    mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp)]

/-- The smooth kernel crosses exactly the zeta pole, with no zeta-zero hypothesis. -/
theorem smoothDetector_finite_rectangle_residue {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hs : tsupport ψ ⊆ Icc a b)
    {ρ : ℂ} {X N q R : ℝ} (hN : 0 < N)
    (hβLower : 3/4 ≤ ρ.re) (hβUpper : ρ.re < 1) (hR : |ρ.im| < R) :
    RectangleIntegral' (smoothDetectorKernel ψ ρ X N q)
      (((1/2-ρ.re : ℝ) : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        smoothDetectorResidue ψ ρ X N q := by
  let l : ℝ := 1/2-ρ.re
  let z : ℂ := (l : ℂ)-(R : ℂ)*I
  let w : ℂ := ((1/2 : ℝ) : ℂ)+(R : ℂ)*I
  let p : ℂ := 1-ρ
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
  have hγLower := (abs_lt.mp hR).1
  have hγUpper := (abs_lt.mp hR).2
  have hzRe : z.re ≤ w.re := by simp [z,w,l]; linarith
  have hzIm : z.im ≤ w.im := by simp [z,w]; linarith
  have hpInterior : Rectangle z w ∈ 𝓝 p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · simp [p,z,w,l]
      constructor <;> linarith
    · simp [p,z,w]
      constructor <;> linarith
  have hcontour := entire_div_sub_rectangle
    (smoothContourNumerator_differentiable hψ ha hs ρ X q hN) hzRe hzIm hpInterior
  rw [smoothContourNumerator_at_pole] at hcontour
  change RectangleIntegral' (smoothDetectorKernel ψ ρ X N q) z w = _
  rw [← hcontour]
  apply RectangleIntegral'_congr
  intro s hsBorder
  have hsp : s ≠ p := by
    intro heq
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds hpInterior (heq ▸ hsBorder)
  exact (smoothContourNumerator_div_eq_kernel ψ ρ X N q hsp).symm

end MathCollab.Density.Stronger
