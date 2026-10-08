module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Stronger.LongScalarBudget
public import MathCollab.Density.Stronger.LongMeanCounting
public import MathCollab.Density.Stronger.SeparatedCriticalSampling

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Pointwise sampling reduction under an explicit bound on the literal
actual-zeta twelfth moment. This does not assert that moment bound. -/
theorem separated_weightedMean_bound_of_twelfth_bound {U : Finset ℝ} {T D ε : ℝ}
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hU : oneSeparated U)
    (hslab : ∀ u ∈ U, u ∈ Icc T (2*T))
    (hmoment : (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ D*T^(2+ε)) :
    (∑ u ∈ U, (weightedCriticalMean 128 u)^12) ≤
      (Real.pi^11*separationMass*D+2*(12:ℝ)^12*Real.pi^12)*T^(2+ε) := by
  have hp : 0 ≤ Real.pi^11*separationMass := mul_nonneg (by positivity) separationMass_nonneg
  have htail : T^(-113 : ℝ) ≤ T^(2+ε) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  apply (separated_weightedCriticalMean_twelfth_le hT hU hslab).trans
  calc
    _ ≤ (Real.pi^11*separationMass)*(D*T^(2+ε)) +
        (2*(12:ℝ)^12*Real.pi^12)*T^(2+ε) :=
      add_le_add (mul_le_mul_of_nonneg_left hmoment hp)
        (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = _ := by ring

/-- Conditional long counting with a retained positive exponent saving.
The only unproved analytic input is displayed literally as `hmoment`.
The bound is uniform in the finite separated set and its sample locations. -/
theorem long_mean_count_eventually_of_twelfth_bound {σ δ ε C D : ℝ}
    (hσ : 3/4 < σ) (hδ : δ < (1-smoothingExponent σ)/12)
    (hε : 0 ≤ ε) (hε' : ε ≤ (1-smoothingExponent σ)/8) (hD : 0 ≤ D)
    (hmoment : ∀ᶠ T : ℝ in atTop,
      (∫ t in Icc 0 (3*T), zetaMomentCriticalNorm t^12) ≤ D*T^(2+ε)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ U : Finset ℝ,
      oneSeparated U → (∀ u ∈ U, u ∈ Icc T (2*T)) →
      (∀ u ∈ U, (detectorY σ T)^((σ-1/2)/2) ≤
        48*C*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean 128 u) →
      (U.card : ℝ) ≤ K*T^(densityExponent σ-(1-smoothingExponent σ)/4) := by
  let P : ℝ := Real.pi^11*separationMass*D+2*(12:ℝ)^12*Real.pi^12
  let B : ℝ := (48*C)^12*P
  have hP : 0 ≤ P := by
    dsimp [P]
    have := separationMass_nonneg
    positivity
  have hB : 0 ≤ B := mul_nonneg (by positivity) hP
  refine ⟨B+1,by linarith,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),hmoment,long_count_scalar_eventually hσ hδ hε']
    with T hT hmomentT hscalar
  intro U hU hslab hmean
  have hTp : 0 < T := by linarith
  have hXp : 0 ≤ detectorX δ T := Real.rpow_nonneg hTp.le _
  have hYp : 0 < detectorY σ T := Real.rpow_pos_of_pos hTp _
  have hcount := long_mean_twelfth_count hXp hYp hmean
  have hsample := separated_weightedMean_bound_of_twelfth_bound hT hε hU hslab hmomentT
  have hpre : (U.card : ℝ)*(detectorY σ T)^(6*σ-3) ≤
      B*((detectorX δ T)^6*(Real.log T)^12*T^(2+ε)) := by
    apply hcount.trans
    calc
      _ ≤ (48*C)^12*(detectorX δ T)^6*(Real.log T)^12*(P*T^(2+ε)) :=
        mul_le_mul_of_nonneg_left hsample (by positivity)
      _ = _ := by dsimp [B]; ring
  have hdiv : (U.card : ℝ) ≤
      B*((detectorX δ T)^6*(Real.log T)^12*T^(2+ε)/(detectorY σ T)^(6*σ-3)) := by
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hYp (6*σ-3))).mpr hpre
    simpa only [mul_div_assoc] using hh
  calc
    _ ≤ B*((detectorX δ T)^6*(Real.log T)^12*T^(2+ε)/(detectorY σ T)^(6*σ-3)) := hdiv
    _ ≤ B*T^(densityExponent σ-(1-smoothingExponent σ)/4) :=
      mul_le_mul_of_nonneg_left hscalar hB
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hTp.le _)

end MathCollab.Density.Stronger
