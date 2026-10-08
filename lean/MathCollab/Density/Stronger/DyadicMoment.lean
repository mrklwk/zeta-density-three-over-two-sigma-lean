module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Filter Set
open scoped Interval ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem exists_dyadic_cutoff {X : ℝ} (hX : 1 ≤ X) :
    ∃ M : ℕ, X ≤ (2:ℝ)^M ∧ (2:ℝ)^M ≤ 2*X := by
  obtain ⟨m,hm,hupper⟩ := exists_nat_pow_near hX (by norm_num : (1:ℝ)<2)
  refine ⟨m+1,hupper.le,?_⟩
  rw [pow_succ']
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

theorem exists_dyadic_count_sq_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ M : ℕ, ((M:ℝ)+1)^2 ≤ D*((2:ℝ)^M)^ε := by
  let a : ℝ := ε/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := 1+1/(a*Real.log 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C^2,pow_pos hC 2,?_⟩
  intro M
  have hp : 1 ≤ ((2:ℝ)^M)^a :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) ha.le
  have hl := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ (2:ℝ)^M) ha
  rw [Real.log_pow] at hl
  have hm : (M:ℝ) ≤ ((2:ℝ)^M)^a/(a*Real.log 2) := by
    apply (le_div_iff₀ (mul_pos ha hlog)).mpr
    have h := (le_div_iff₀ ha).mp hl
    nlinarith
  have hcount : (M:ℝ)+1 ≤ C*((2:ℝ)^M)^a := by
    calc
      _ ≤ ((2:ℝ)^M)^a/(a*Real.log 2)+((2:ℝ)^M)^a := add_le_add hm hp
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ (C*((2:ℝ)^M)^a)^2 :=
      pow_le_pow_left₀ (by positivity) hcount 2
    _ = _ := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^M)]
      congr 2
      dsimp [a]
      norm_num


/-- A nonnegative continuous function with a dyadic power bound has the
corresponding bound from zero. The compact initial interval is retained. -/
theorem integral_zero_le_of_dyadic (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {p B C : ℝ} (hp : 1 ≤ p) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hdyad : ∀ H : ℝ, B ≤ H → (∫ t in H..2*H, f t) ≤ C*H^p) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, B ≤ H →
      (∫ t in 0..H, f t) ≤ K*H^p := by
  let A : ℝ := |∫ t in 0..B, f t| + C + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hCA : C ≤ A := by dsimp [A]; linarith [abs_nonneg (∫ t in 0..B, f t)]
  have hBp : 0 < B := by linarith
  have htwo : (2 : ℝ) ≤ (2 : ℝ)^p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  have hstep : ∀ m : ℕ, (∫ t in 0..(2 : ℝ)^m*B, f t) ≤ A*((2 : ℝ)^m*B)^p := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, one_mul]
      have hbpower := Real.one_le_rpow hB (by linarith : 0 ≤ p)
      calc
        _ ≤ |∫ t in 0..B, f t| := le_abs_self _
        _ ≤ A := by dsimp [A]; linarith
        _ ≤ A*B^p := by nlinarith
    | succ m ih =>
      have hm : B ≤ (2 : ℝ)^m*B := by
        have hpow : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
        nlinarith
      have hX : 0 ≤ (2 : ℝ)^m*B := by positivity
      have heq : (2 : ℝ)^(m+1)*B = 2*((2 : ℝ)^m*B) := by rw [pow_succ']; ring
      rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 ((2 : ℝ)^m*B))
        (hf.intervalIntegrable ((2 : ℝ)^m*B) (2*((2 : ℝ)^m*B)))]
      calc
        _ ≤ A*((2 : ℝ)^m*B)^p + C*((2 : ℝ)^m*B)^p :=
          add_le_add ih (hdyad _ hm)
        _ ≤ A*((2 : ℝ)^m*B)^p + A*((2 : ℝ)^m*B)^p :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg hX _))
        _ = A*2*((2 : ℝ)^m*B)^p := by ring
        _ ≤ A*(2 : ℝ)^p*((2 : ℝ)^m*B)^p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo hA.le)
            (Real.rpow_nonneg hX _)
        _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX]; ring
  refine ⟨A*(2 : ℝ)^p, by positivity, ?_⟩
  intro H hH
  have hHp : 0 < H := hBp.trans_le hH
  obtain ⟨m, hlo, hhi⟩ := exists_dyadic_cutoff
    ((le_div_iff₀ hBp).mpr (by simpa using hH))
  have hlo' : H ≤ (2 : ℝ)^m*B := (div_le_iff₀ hBp).mp hlo
  have hhi' : (2 : ℝ)^m*B ≤ 2*H := by
    have := (mul_le_mul_iff_left₀ hBp).mpr hhi
    field_simp at this
    nlinarith
  calc
    _ ≤ ∫ t in 0..(2 : ℝ)^m*B, f t := by
      apply intervalIntegral.integral_mono_interval le_rfl hHp.le hlo'
      · exact Filter.Eventually.of_forall hf0
      · exact hf.intervalIntegrable _ _
    _ ≤ A*((2 : ℝ)^m*B)^p := hstep m
    _ ≤ A*(2*H)^p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhi' (by linarith)) hA.le
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hHp.le]; ring



end MathCollab.Density.Stronger
