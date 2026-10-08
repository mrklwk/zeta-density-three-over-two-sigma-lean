# A zero-density estimate with exponent 3(1−σ)/(2σ) for the Riemann zeta function

For every real $\sigma>3/4$ and $\varepsilon>0$, the formalization proves that
there exists $C_{\sigma,\varepsilon}>0$ such that, for every real $T\ge2$,

$$
N(\sigma,T)\le C_{\sigma,\varepsilon}
T^{3(1-\sigma)/(2\sigma)+\varepsilon}.
$$

Here $N(\sigma,T)$ counts **all** zeros $\rho$ of the Riemann zeta function with
$\Re\rho\ge\sigma$ and $|\Im\rho|\le T$, with their positive finite analytic
multiplicities. Both boundaries and both signs of the ordinate are included.
The constant is fixed before all heights $T$. The count is empty for $\sigma\ge1$.

The proof combines a separately proved **Type I large-values theorem for
Dirichlet polynomials**, controlling short detector pieces, with the
**critical-line twelfth moment**, controlling long pieces. Both inputs are
proved in Lean; the final density theorem has no assumed growth, moment,
point-mean, or stationary-source premise. See the [proof guide](docs/PROOF_GUIDE.md).

The package also proves that, for every real $\varepsilon>0$, there exist
$K_\varepsilon>0$ and $T_0$ such that every real $T\ge T_0$ satisfies

$$
\int_{[0,3T]}|\zeta(1/2+it)|^{12}\,dt\le K_\varepsilon T^{2+\varepsilon}.
$$

The public statements are [DensityStronger.density_bound](lean/Solution.lean)
and [DensityStronger.twelfth_moment](lean/Solution.lean). They use mathlib's
actual `riemannZeta`, `analyticOrderNatAt`, and Lebesgue integral. The theorem
excludes $\sigma=3/4$ and $\varepsilon=0$ and does not give effective constants
or uniformity at the parameter boundaries. It does not assert the full density
hypothesis for $\sigma>1/2$ or the exact logarithmic refinement of the moment.

## Comparison with existing estimates

Compared with the estimates in Tao–Trudgian–Yang's Table 2 and Kerr's public
preprint, the leading exponent improves strictly for
$3/4<\sigma<23/29$ ($0.75<\sigma<0.7931034483\ldots$), agrees with the best
located leading exponent for $23/29\le\sigma\le7/8$, and is weaker than
existing estimates for $7/8<\sigma<1$. This comparison includes Kerr's
preprint and concerns leading powers of $T$, not identical constants or
logarithmic factors. [Sources and calculation](docs/LITERATURE.md).

## Build and verification

The Lake project is in `lean/`, pinned to **Lean 4.35.0-rc2** and
mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
cd lean
lake build MathCollab Solution
```

The production proofs contain no `sorry`, admitted result, or custom axiom.
The two intentional holes in [Challenge.lean](lean/Challenge.lean) are independent
specifications for the Comparator and are not imported by production proofs.
The checked dependency closures use only `propext`, `Classical.choice`, and
`Quot.sound`. Source builds, semantic checks, kernel replay and the official
sandboxed Comparator passed for the recorded prior source snapshot. This copy
changes only comments in 19 Lean files; all non-comment Lean source is unchanged.
Checks of this package are recorded in the accompanying source-bound verification
receipts.
[Verification scope and reproduction](docs/VERIFICATION.md).

The proof itself is Lean source. [Theorem map](docs/THEOREM_MAP.md),
[moment API](docs/MOMENT_API.md), and [stationary endpoints](docs/STATIONARY_ENDPOINTS.md)
describe reusable interfaces.

## Attribution and license

Original contributions are **AGPL-3.0-only**. Substantial selected proofs from
Scott McColm, Conor Grogan, PrimeNumberTheoremAnd contributors, and mathlib
retain their MIT, MIT-0 and Apache-2.0 licenses and notices. Material AI
assistance is disclosed in [CREDITS.md](CREDITS.md).
[Source provenance](PROVENANCE.md), [licensing scope](LICENSE_STATUS.md),
[NOTICE](NOTICE), and [LICENSE](LICENSE) give the details.
