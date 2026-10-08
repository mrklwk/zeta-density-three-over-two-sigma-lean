module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under MIT-0.
Single shared copy of the cutoff bound previously duplicated in PhysicalBudget
and StationarySumScale; theorem statement and proof text preserved exactly.
Source pin: 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPhysicalCutoff

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonSourceCutoff_le_natural {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hupper : G ≤ Real.sqrt T) (hL : 1 ≤ L) :
    (atkinsonSourceCutoff T G L : ℝ) ≤ 37*T*L^2/G^2 := by
  have hT0 : 0 < T := by linarith
  have hG2 : 0 < G^2 := sq_pos_of_pos hG
  have hGT : G^2 ≤ T := by nlinarith [Real.sq_sqrt hT0.le]
  have hL2 : 1 ≤ L^2 := by nlinarith
  have hU : 1 ≤ T*L^2/G^2 := (le_div_iff₀ hG2).2 (by nlinarith)
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 36*T*(L/G)^2)
  change (atkinsonSourceCutoff T G L : ℝ) < 36*T*(L/G)^2+1 at hceil
  have he : 36*T*(L/G)^2 = 36*(T*L^2/G^2) := by ring
  rw [he] at hceil
  have he' : 37*T*L^2/G^2 = 37*(T*L^2/G^2) := by ring
  rw [he']
  linarith

end MathCollab.Density.Stronger.Atkinson
