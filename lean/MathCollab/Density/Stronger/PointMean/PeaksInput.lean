module
-- Reversible module-visibility port of the audited development.
/- Native point-mean producer for the actual finite-peak interface. -/
public import MathCollab.Density.Stronger.PointMean.Equation44
public import MathCollab.Density.Stronger.Peaks.Inputs

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The analytic point-to-local-second-mean input is proved by the actual
Gamma-zeta-square contour and exponential-overlap chain. -/
theorem pointMeanInput_native : Peaks.PointMeanInput :=
  heathBrown_equation44_native

end MathCollab.Density.Stronger.PointMean
