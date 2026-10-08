# Moment API

## Direct fourth and twelfth moments

### `Fourth.zeta_fourth_dyadic`

Explicit fourth-moment threshold; C is nonnegative, and H is required positive. Source: [Fourth/FourthMoment.lean](../lean/MathCollab/Density/Stronger/Fourth/FourthMoment.lean#L25).

```lean
theorem zeta_fourth_dyadic :
    ∀ η : ℝ, 0 < η → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η)
```

### `actual_fourth_moment_eventually`

Eventual fourth-moment adapter used by the native twelfth-moment producer. Source: [MomentFromPeaks.lean](../lean/MathCollab/Density/Stronger/MomentFromPeaks.lean#L19).

```lean
theorem actual_fourth_moment_eventually (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η)
```

### `zeta_twelfth_dyadic_native`

Actual twelfth moment on the oriented interval H..2*H, at sufficiently large positive heights; D is positive. Source: [NativeMoment.lean](../lean/MathCollab/Density/Stronger/NativeMoment.lean#L21).

```lean
theorem zeta_twelfth_dyadic_native :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε)
```

### `zeta_twelfth_physical_native`

Actual twelfth moment over the set Icc 0 (3*T), including the compact initial interval; K is positive. This is the exact interface consumed by density counting. Source: [NativeMoment.lean](../lean/MathCollab/Density/Stronger/NativeMoment.lean#L29).

```lean
theorem zeta_twelfth_physical_native :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε)
```

## Native high-value interfaces

The original physical heights remain in `pointValueSuperlevel H V`:
`H ≤ t ∧ t ≤ 2*H ∧ V ≤ zetaMomentCriticalNorm t`. `oneSeparated W` is the
original pairwise unit-separation condition. Both parity classes and all
occupancy levels have already been aggregated; these statements concern the
whole W and the whole superlevel set.

### `pointValue_peak_card_native`

Source: [NativePeaks.lean](../lean/MathCollab/Density/Stronger/NativePeaks.lean#L25).

```lean
theorem pointValue_peak_card_native :
    ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V → ∀ W : Finset ℝ,
      oneSeparated W → (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η)
```

### `pointValue_volume_native`

Source: [NativePeaks.lean](../lean/MathCollab/Density/Stronger/NativePeaks.lean#L34).

```lean
theorem pointValue_volume_native :
    ∀ η : ℝ, 0 < η → ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,
      0 < V → H^(1/8+η) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+η)/V^12)
```

## Native second-moment and point-mean support

These are supporting local second-moment interfaces, not additional global
second-moment asymptotics. They have actual proved producers.

### `PointMean.heathBrownLemmaThree_native`

The closed type is `PointMean.HeathBrownLemmaThree`. Its transparent definition
and literal weighted moment are:

```lean
noncomputable def heathBrownLemmaThreeMoment (t L : ℝ) : ℝ :=
  ∫ u in -L..L,
    Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

/-- Heath--Brown (1978), Lemma 3, with an explicit absolute constant. -/
def HeathBrownLemmaThree : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 10 ≤ t →
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t *
          (1 + heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)))
```

Producer: [PointMean/Native.lean](../lean/MathCollab/Density/Stronger/PointMean/Native.lean#L264).

### `PointMean.heathBrown_equation44_native`

Source: [PointMean/Equation44.lean](../lean/MathCollab/Density/Stronger/PointMean/Equation44.lean#L104).

```lean
theorem heathBrown_equation44_native :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T V center G L : ℝ) (W : Finset ℝ),
        10 ≤ T → 0 < V → 0 ≤ G → 0 ≤ L →
        oneSeparated W →
        (∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2) →
        10 ≤ center - G / 2 → center + G / 2 ≤ T →
        (∀ t ∈ W, Real.log t ^ (2 : ℕ) ≤ L) →
        G / 2 + L ≤ G →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        V ^ (2 : ℕ) * (W.card : ℝ) ≤
          C * Real.log T *
            ((W.card : ℝ) + 4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ)))
```

### `Atkinson.exists_zetaSquareLocalMean_le_atkinson_stationary`

Source: [Atkinson/AtkinsonNativeLocalMean.lean](../lean/MathCollab/Density/Stronger/Atkinson/AtkinsonNativeLocalMean.lean#L24).

```lean
theorem exists_zetaSquareLocalMean_le_atkinson_stationary {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → T ^ (1 / 4 + κ) ≤ G →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (atkinsonStationaryLeadingSum T G (Real.log T)).re +
          C * G * Real.log T
```

`PointMean.pointMeanInput_native : Peaks.PointMeanInput` is the proved packet
adapter for the preceding equation. `Atkinson.localMeanStationaryInput_native :
Atkinson.LocalMeanStationaryInput` is the closed adapter for the preceding local
source inequality. `localMeanPacketInput_of_stationary` supplies the packet bound
when applied to that actual native source producer.

Conditional helpers such as `zeta_twelfth_physical_of_peak_card`,
`zeta_twelfth_dyadic_of_fourth_and_tail`, and
`stronger_density_bound_of_twelfth_moment` retain their displayed hypotheses.
The native endpoints above supply those hypotheses. This inventory does not
add new interpolated sixth/eighth-moment results or a global [0,T] fourth-moment
wrapper; no such new theorem was introduced for this documentation task.
