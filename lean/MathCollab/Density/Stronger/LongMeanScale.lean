module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.WeightedCriticalMean

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Division-free form of the detecting mean inequality, convenient for
raising to the twelfth power without requiring a positive mollifier cutoff. -/
theorem weightedCriticalMean_detecting_scale {A : ℕ} {C X N T β γ : ℝ}
    (hT : 1 < T) (hN : 0 < N)
    (hmean : 1/(48*Real.log T) ≤ C*Real.sqrt X*N^(1/2-β)*weightedCriticalMean A γ) :
    N^(β-1/2) ≤ 48*C*Real.sqrt X*Real.log T*weightedCriticalMean A γ := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hp : N^(1/2-β)*N^(β-1/2) = 1 := by
    rw [← Real.rpow_add hN]
    simp
  have hh := mul_le_mul_of_nonneg_right hmean (Real.rpow_nonneg hN.le (β-1/2))
  have he : (C*Real.sqrt X*N^(1/2-β)*weightedCriticalMean A γ)*N^(β-1/2) =
      C*Real.sqrt X*weightedCriticalMean A γ := by
    calc
      _ = C*Real.sqrt X*weightedCriticalMean A γ*(N^(1/2-β)*N^(β-1/2)) := by ring
      _ = _ := by rw [hp,mul_one]
  rw [he] at hh
  have hd : N^(β-1/2)/(48*Real.log T) ≤ C*Real.sqrt X*weightedCriticalMean A γ := by
    simpa only [one_div,inv_mul_eq_div] using hh
  have hh' := (div_le_iff₀ (by positivity : 0 < 48*Real.log T)).mp hd
  convert hh' using 1
  ring

/-- A long block N≥sqrt(Y) gives the precise lower scale power needed by the
twelfth-moment counting argument; this lemma assumes no moment estimate. -/
theorem weightedCriticalMean_long_scale {A : ℕ} {C X N Y T σ β γ : ℝ}
    (hT : 1 < T) (hN : 1 ≤ N) (hY : 0 < Y) (hσ : 1/2 ≤ σ) (hβ : σ ≤ β)
    (hlong : Real.sqrt Y ≤ N)
    (hmean : 1/(48*Real.log T) ≤ C*Real.sqrt X*N^(1/2-β)*weightedCriticalMean A γ) :
    Y^((σ-1/2)/2) ≤ 48*C*Real.sqrt X*Real.log T*weightedCriticalMean A γ := by
  have hNp : 0 < N := by linarith
  calc
    Y^((σ-1/2)/2) = (Real.sqrt Y)^(σ-1/2) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hY.le]
      congr 1
      ring
    _ ≤ N^(σ-1/2) := Real.rpow_le_rpow (Real.sqrt_nonneg _) hlong (by linarith)
    _ ≤ N^(β-1/2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ ≤ _ := weightedCriticalMean_detecting_scale hT hNp hmean

end MathCollab.Density.Stronger
