# Exact stationary error endpoints

Namespace `MathCollab.Density.Stronger.Atkinson`.
These source statements use the original literal series and cutoff.

Source: [Atkinson/AtkinsonStationarySumError.lean](../lean/MathCollab/Density/Stronger/Atkinson/AtkinsonStationarySumError.lean#L40).

```lean
theorem exists_atkinsonLeadingSum_sub_stationary_above_fourthRoot {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      ‖atkinsonLeadingSum T G (Real.log T)-atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G
```

Source: [Atkinson/AtkinsonTwoTermStationary.lean](../lean/MathCollab/Density/Stronger/Atkinson/AtkinsonTwoTermStationary.lean#L49).

```lean
theorem exists_tsum_zetaAtkinsonTwoTerm_sub_stationary_above_fourthRoot
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → T ^ (1 / 4 + κ) ≤ G →
      ‖(∑' n : ℕ, zetaAtkinsonTwoTerm T G (Real.log T) n) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ C * G
```
