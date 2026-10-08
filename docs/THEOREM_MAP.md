# Theorem map

Names below are relative to `MathCollab.Density.Stronger`
unless otherwise stated. Importing `MathCollab.Density.Stronger.NativeDensity`
exposes the completed chain; use the narrower modules below for reuse.

## Final count and its meaning

[lean/MathCollab/Density/Stronger/NativeDensity.lean](../lean/MathCollab/Density/Stronger/NativeDensity.lean):

```lean
theorem stronger_density_bound_native {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(3*(1-σ)/(2*σ)+ε)
```

The definitions in
[lean/MathCollab/Density/ZetaCounting.lean](../lean/MathCollab/Density/ZetaCounting.lean)
are in namespace `MathCollab.Density`:

| Name | Meaning |
| --- | --- |
| `zetaMultiplicity ρ` | `analyticOrderNatAt riemannZeta ρ`; finite and positive at counted zeros. |
| `zetaZeroFinset σ a b` | Every actual nontrivial zero with `σ ≤ ρ.re` and `a ≤ ρ.im ≤ b`. |
| `zetaSlabCount σ a b` | Sum of those analytic multiplicities. |
| `zetaDensityCount σ T` | `zetaSlabCount σ (-T) T`. |

For `σ>3/4`, the strip predicate excludes no actual zero satisfying the stated
real-part and height constraints. The count is not a distinct-ordinate count.
The `σ≥1` case is empty; the nonempty case uses the native twelfth moment and
retains both the bounded-height contribution and the dyadic height sum.

## Direct moment API

The shared integrand, from
[lean/MathCollab/Density/Stronger/CriticalMoment.lean](../lean/MathCollab/Density/Stronger/CriticalMoment.lean), is

```lean
def zetaMomentCriticalNorm (t : ℝ) : ℝ :=
  ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
```

`∀ᶠ H in atTop` means all sufficiently large real heights. Constants and
thresholds may depend on the positive loss exponent; no numerical values or
uniformity as the loss tends to zero are asserted.

[lean/MathCollab/Density/Stronger/Fourth/FourthMoment.lean](../lean/MathCollab/Density/Stronger/Fourth/FourthMoment.lean), namespace `Fourth`:

```lean
theorem zeta_fourth_dyadic :
    ∀ η : ℝ, 0 < η → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η)
```

`actual_fourth_moment_eventually` in
[lean/MathCollab/Density/Stronger/MomentFromPeaks.lean](../lean/MathCollab/Density/Stronger/MomentFromPeaks.lean)
puts this in eventual form, still with a nonnegative constant.

[lean/MathCollab/Density/Stronger/NativeMoment.lean](../lean/MathCollab/Density/Stronger/NativeMoment.lean):

```lean
theorem zeta_twelfth_dyadic_native :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε)

theorem zeta_twelfth_physical_native :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ K*T^(2+ε)
```

The second statement includes the compact initial interval. These native
endpoints have no analytic-input parameter. This map does not assert additional
interpolated moment theorems or a separately proved global fourth-moment wrapper.

## Native analytic inputs and their consumers

| Interface | Role and source |
| --- | --- |
| `Atkinson.ordinaryDivisorVoronoi_native` | Actual compact-test q=1 Voronoi identity, including both complete dual series. [OrdinaryDivisorVoronoi.lean](../lean/MathCollab/Density/Stronger/Atkinson/OrdinaryDivisorVoronoi.lean). |
| `Atkinson.localMeanStationaryInput_native` | Closed producer for the literal local second moment and exact signed stationary sum. [AtkinsonNativeLocalMean.lean](../lean/MathCollab/Density/Stronger/Atkinson/AtkinsonNativeLocalMean.lean). |
| `Atkinson.localMeanPacketInput_of_stationary` | Applies the exact source to signed prefix/Gram estimates. Its source parameter is filled by the preceding producer. [AtkinsonStationarySourceAssembly.lean](../lean/MathCollab/Density/Stronger/Atkinson/AtkinsonStationarySourceAssembly.lean). |
| `PointMean.heathBrownLemmaThree_native` | Actual weighted local second moment controls the point value for every `t≥10`. [PointMean/Native.lean](../lean/MathCollab/Density/Stronger/PointMean/Native.lean); transparent statement in [PointMean/Statement.lean](../lean/MathCollab/Density/Stronger/PointMean/Statement.lean). |
| `PointMean.heathBrown_equation44_native`, `PointMean.pointMeanInput_native` | Finite-peak overlap bound and its packet interface. [Equation44.lean](../lean/MathCollab/Density/Stronger/PointMean/Equation44.lean), [PeaksInput.lean](../lean/MathCollab/Density/Stronger/PointMean/PeaksInput.lean). |
| `pointValue_peak_card_native` | Eventually, every one-separated finite subset of the actual high-value set satisfies `card(W)*V^12 ≤ H^(2+η)` when `V≥H^(1/8+η)>0`. [NativePeaks.lean](../lean/MathCollab/Density/Stronger/NativePeaks.lean). |
| `pointValue_volume_native` | Measure of the same full superlevel set is at most `2*H^(2+η)/V^12`. [NativePeaks.lean](../lean/MathCollab/Density/Stronger/NativePeaks.lean). |
| `stronger_density_bound_of_twelfth_moment` | Detector and counting consumer whose displayed moment premise is discharged in `NativeDensity`. [ConditionalDensity.lean](../lean/MathCollab/Density/Stronger/ConditionalDensity.lean). |

The high-value set is exactly `H ≤ t ∧ t ≤ 2*H ∧ V ≤ zetaMomentCriticalNorm t`.
Its eventual threshold precedes `V` and the finite set. The moment reconstruction
combines its measure bound with the actual fourth moment, then performs the
high/low split and dyadic summation. Conditional helper files retain their
explicit premises; a conditional helper alone is not the native endpoint.
