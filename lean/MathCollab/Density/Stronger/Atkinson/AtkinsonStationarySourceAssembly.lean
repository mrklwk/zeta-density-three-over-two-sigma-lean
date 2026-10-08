module
-- Reversible module-visibility port of the audited development.
/-
Exact stationary-source-to-prefix assembly using the narrowly ported McColm
source at 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. The actual stationary sum
and all analytic estimates it consumes retain MIT-0 attribution in
third_party/twelfth/LICENSE-MIT-0. Mathlib retains Apache-2.0 attribution.
This conditional adapter retains the local source premise. Its proved producer
is localMeanStationaryInput_native in AtkinsonNativeLocalMean.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryDyadic
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSourceAssembly

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- The literal local-zeta-to-stationary-source interface, proved in
AtkinsonNativeLocalMean and retained here as a reusable conditional input.
Its constant and threshold precede both physical variables. -/
def LocalMeanStationaryInput : Prop :=
  ∀ δ κ : ℝ, 0 < δ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ t G : ℝ,
      T₀ ≤ t → t^δ ≤ G → G ≤ t^(1/2-δ) → t^(1/4+κ) ≤ G →
      (∫ u in t-G..t+G, zetaMomentCriticalNorm u^2) ≤
        2*Real.exp 1*(atkinsonStationaryLeadingSum t G (Real.log t)).re +
          C*G*Real.log t

/-- Conditional only on the actual-zeta source approximation. Stationary
normalization, both signed weight variations, and prefix control are proved. -/
theorem localMeanSourceToPrefix_of_stationary (hSource : LocalMeanStationaryInput) :
    LocalMeanSourceToPrefix := by
  intro δ κ hδ hκ
  obtain ⟨A,hA,U,hU,hsource⟩ := hSource δ κ hδ hκ
  obtain ⟨B,hB,V,hV,hstationary⟩ := exists_norm_atkinsonStationarySum_le_undamped hδ
  let C : ℝ := A+2*Real.exp 1*B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,max U V,hU.trans (le_max_left _ _),?_⟩
  intro t G ht hlower hupper hquarter
  have htU : U ≤ t := (le_max_left _ _).trans ht
  have htV : V ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := by linarith [hU.trans htU]
  have hG : 0 < G := (Real.rpow_pos_of_pos ht0 δ).trans_le hlower
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith [hU.trans htU])
  have hprefix := atkinsonUndampedDyadicPhaseBound_nonneg t
    (atkinsonSourceCutoff t G (Real.log t))
  have hs := (Complex.re_le_norm (atkinsonStationaryLeadingSum t G (Real.log t))).trans
    (hstationary t G htV hlower hupper)
  have hmain := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*Real.exp 1)
  have hA' : A ≤ C := le_add_of_nonneg_right (by positivity)
  have hB' : 2*Real.exp 1*B ≤ C := by dsimp [C]; linarith
  have hterm :
      (2*Real.exp 1*B)*G*t^(-(1/4:ℝ))*
        atkinsonUndampedDyadicPhaseBound t (atkinsonSourceCutoff t G (Real.log t)) ≤
      C*G*t^(-(1/4:ℝ))*
        atkinsonUndampedDyadicPhaseBound t (atkinsonSourceCutoff t G (Real.log t)) := by
    gcongr
  have herror : A*G*Real.log t ≤ C*G*Real.log t := by gcongr
  have hactual := hsource t G htU hlower hupper hquarter
  nlinarith

/-- Native packet estimates require only the remaining actual source approximation. -/
theorem localMeanPacketInput_of_stationary (hSource : LocalMeanStationaryInput) :
    Peaks.LocalMeanPacketInput :=
  localMeanPacketInput_of_sourceToPrefix (localMeanSourceToPrefix_of_stationary hSource)

end MathCollab.Density.Stronger.Atkinson
