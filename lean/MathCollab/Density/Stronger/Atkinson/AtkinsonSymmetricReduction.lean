module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected proof slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow stationary refinement; see third_party/twelfth/ATKINSON_SYMMETRIC_MANIFEST.json.
Mathlib and previously ported PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSymmetricStationary
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryMain

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Full carrier approximation after exact odd cancellation

The actual tails and evaluated Fresnel value are retained. The improved
local error is consumed at the original positive-support carrier, with
its true amplitude and a uniform constant for each fixed power.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonSymmetricError (T b R H : ℝ) : ℝ :=
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  4/(H*Real.pi) + 4*R^2*H^3 + 8*R*T*H^5/r^3 +
    16*T*H^5/r^4 + 16*T^2*H^7/r^6

theorem atkinsonSymmetricError_tail_le {T R H : ℝ} (hT : 0 < T)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (b : ℝ) :
    4/(H*Real.pi) ≤ atkinsonSymmetricError T b R H := by
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T/(2*Real.pi)) b
  unfold atkinsonSymmetricError
  have h1 : 0 ≤ 4*R^2*H^3 := by positivity
  have h2 : 0 ≤ 8*R*T*H^5/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 := by positivity
  have h3 : 0 ≤ 16*T*H^5/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^4 := by positivity
  have h4 : 0 ≤ 16*T^2*H^7/(atkinsonSaddleRoot (T/(2*Real.pi)) b)^6 := by positivity
  linarith

theorem IntervalC2Bound.atkinsonSymmetricApproximation {f : ℝ → ℂ}
    {a c M R T H : ℝ} (hf : IntervalC2Bound f a c M R)
    (hv : IntervalC1Bound f a c M) (hT : 0 < T) (b : ℝ)
    (ha : 0 < a) (hH : 0 < H)
    (hleft : a ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b-H)
    (hright : atkinsonSaddleRoot (T/(2*Real.pi)) b+H ≤ c)
    (hwindow : H ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b/2) :
    ‖(∫ y in a..c, f y*atkinsonRootKernel T b y) -
      f (atkinsonSaddleRoot (T/(2*Real.pi)) b) *
        ∫ y in (atkinsonSaddleRoot (T/(2*Real.pi)) b-H)..
          (atkinsonSaddleRoot (T/(2*Real.pi)) b+H), atkinsonRootQuadraticKernel T b y‖ ≤
      (M/2)*atkinsonSymmetricError T b R H := by
  have hlocal := hf.atkinsonLocalSymmetric hT b hH.le hleft hright hwindow
  have htail := hv.atkinsonRoot_sub_local hT b ha hH hleft hright
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add htail hlocal).trans_eq ?_)
  unfold atkinsonSymmetricError
  ring

theorem exists_atkinsonPowerIntegral_finite_symmetric_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G^2 ≤ 2*T →
      1 ≤ L → 8*L ≤ G → 0 < H →
      Real.sqrt T/4 ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b-H →
      atkinsonSaddleRoot (T/(2*Real.pi)) b+H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b/2 →
      ‖atkinsonPowerIntegral T G L α b-atkinsonFiniteStationaryMain T G L α b H‖ ≤
        C*G*T^(-α)*atkinsonSymmetricError T b (G/Real.sqrt T) H := by
  obtain ⟨A,hA,hv⟩ := exists_intervalC1Bound_atkinsonPowerWeight_root α
  obtain ⟨B,hB,hf⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural α
  refine ⟨A+B,by positivity,?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hAM : A*G*T^(-α) ≤ (A+B)*G*T^(-α) := by gcongr; linarith
  have hBM : B*G*T^(-α) ≤ (A+B)*G*T^(-α) := by gcongr; linarith
  have h := ((hf T G L hT hG hGT hL hwidth).mono hBM le_rfl).atkinsonSymmetricApproximation
    ((hv T G L hT hG0 hGT hL0).mono hAM) hT b (by positivity) hH hleft hright hwindow
  have hs : Real.sqrt (T/16) = Real.sqrt T/4 := by rw [Real.sqrt_div hT.le]; norm_num
  rw [atkinsonFiniteStationaryMain_eq_quadratic,
    atkinsonPowerIntegral_eq_root hT hG0 hL0 hwidth α b,hs]
  have he (x y z : ℂ) : 2*x-2*y*z = 2*(x-y*z) := by ring
  rw [he,norm_mul,Complex.norm_ofNat]
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)).trans_eq
  ring

theorem exists_atkinsonPowerIntegral_symmetric_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G^2 ≤ 2*T →
      1 ≤ L → 8*L ≤ G → 0 < H →
      Real.sqrt T/4 ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b-H →
      atkinsonSaddleRoot (T/(2*Real.pi)) b+H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b/2 →
      ‖atkinsonPowerIntegral T G L α b-atkinsonStationaryMain T G L α b‖ ≤
        C*G*T^(-α)*atkinsonSymmetricError T b (G/Real.sqrt T) H := by
  obtain ⟨A,hA,hfinite⟩ := exists_atkinsonPowerIntegral_finite_symmetric_approximation α
  obtain ⟨B,hB,hmain⟩ := exists_norm_atkinsonFiniteStationaryMain_sub_main_le α
  refine ⟨A+B,by positivity,?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hf := hfinite T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hm := hmain T G L b H hT hG0 hGT hL0 hH ⟨by linarith,by linarith⟩
  have hm' := hm.trans (mul_le_mul_of_nonneg_left
    (atkinsonSymmetricError_tail_le (R := G/Real.sqrt T) hT (by positivity) hH.le b)
    (by positivity))
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hf hm').trans_eq ?_)
  ring

end MathCollab.Density.Stronger.Atkinson
