# Source provenance and modifications

This development combines local proofs with substantial selected proof reuse. The imports of the public Lean project are local modules
and the packages pinned in `lean/lake-manifest.json`; no whole upstream
repository is imported as an additional theorem library.

| Source | Pinned revision | Scope and license |
| --- | --- | --- |
| [Scott McColm, Lean](https://github.com/smccolm/Lean) | `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be` | Selected oscillatory, Abel/Jensen and contour proofs; MIT, with inherited Apache-2.0 material separately credited |
| [Scott McColm, Lean](https://github.com/smccolm/Lean) | `6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1` | Selected Weyl, moment, point-mean, Bessel and Atkinson proofs; MIT-0, with selected inherited Apache-2.0 material |
| [Conor Grogan, prime-minor-arcs-2-15](https://github.com/jconorgrogan/prime-minor-arcs-2-15) | `f369f267b4dcfebf010c8e7baa2c9602e2960eba` | Selected Fourier, Poisson, Mellin and Gamma proofs; Apache-2.0 |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `4ecb950126c4290293c5662dfe0e884123171df5` as documented by the vendor | Selected analytic foundations, including digamma; Apache-2.0. See the hash qualification below |

Adaptations extract the needed declarations, replace imports, remove unrelated
blueprint dependencies, adjust namespaces and visibility, and port APIs to the
pinned Lean/mathlib versions. Local work supplies analytic convergence and
contour bridges, source identities, detector families, multiplicity counting,
uniform thresholds and final composition. Names of classical theorems or
modules alone are not claims of whole-paper fidelity.

The portable source records in `third_party/` preserve source filenames, hashes,
selected declaration/range information where available, and licenses. Records
may include inspected dependencies; they do not mean that each listed upstream
file was copied in full. File-level copyright and modification notices and all
retained license texts remain authoritative.

The selected PNT digamma source has SHA-256
`32923ce2c186655e972ea123a42a953f2fb97f83e61c32f143a554e2d307befc`.
The vendor manifest instead recorded
`496eb57daedb46fe25b84da2ef885ed68786265a3337d3a739e0f30228f2970f`.
The selected bytes and Robby Sneiderman's attribution are retained; the vendor's
stated revision is not an unqualified byte-identity assertion.
[Digamma provenance](third_party/twelfth/DIGAMMA_PORT_MANIFEST.json).

The six `GuthMaynard/` modules provide classical exponential-sum and Weyl
machinery used by the detector. Their directory name does not assert that the
entire Guth–Maynard large-values theorem is imported. `WeylPort/` contains the
actual-zeta connection and supporting analytic adaptations.

[CREDITS.md](CREDITS.md) records contribution credits and material AI assistance. [The literature comparison](docs/LITERATURE.md)
separately identifies the mathematical benchmarks.
