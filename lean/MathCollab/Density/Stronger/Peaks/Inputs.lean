module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/PEAK_AGGREGATION_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
PointMeanInput is supplied by PointMean.PeaksInput. LocalMeanPacketInput is
reduced to the stationary source inequality by Atkinson.AtkinsonSourceAssembly.
No unconditional high-value, twelfth-moment or stronger-density bound is asserted.
-/
public import MathCollab.Density.Stronger.MomentGrowth
public import MathCollab.Density.Stronger.AtkinsonGlobalCardinality
public import WeylPort.GrowthAlgebra

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology Finset
open scoped Interval
open MathCollab.Density MathCollab.Density.Stronger
open TaoTrudgianYang2025 (eventually_const_log_pow_le_rpow
  eventually_const_height_log_pow_mul_rpow_le_rpow
  eventually_pointValue_sixth_power_source_range)
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Peaks
def separatedAt (G : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → G ≤ dist x y

def atkinsonLocalMeanExcess (G t error : ℝ) : ℝ :=
  max 0 ((∫ u in t-G..t+G, zetaMomentCriticalNorm u^2)-error)

/-- Analytic point-to-local interface, proved by PointMean.pointMeanInput_native. -/
def PointMeanInput : Prop :=

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

/-- Explicit, currently unproved physical packet input, with constants
chosen before height, width, localization interval and finite set. -/
def LocalMeanPacketInput : Prop :=
  ∀ δ κ ν : ℝ, 0 < δ → 0 < κ → 0 < ν →
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → separatedAt G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L))

end MathCollab.Density.Stronger.Peaks
