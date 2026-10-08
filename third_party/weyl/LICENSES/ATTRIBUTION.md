# Upstream attribution and modification notice

The classical exponential-sum files under `GuthMaynard/`, the selected AFE files under `WeylPort/AFE/`, the complex Laplace extraction, and selected growth/occupancy algebra derive from S. McColm's `smccolm/Lean` repository at commit `6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1`. The upstream license is MIT No Attribution (MIT-0), preserved in `McColm-MIT-0.txt`.

The extracted nonstationary-phase, Euler–Maclaurin, zeta-continuation, and digamma proofs derive from the PrimeNumberTheoremAnd project at commit `4ecb950126c4290293c5662dfe0e884123171df5`, some through McColm's vendored adaptations. Its Apache 2.0 license is preserved in `PNT-Apache-2.0.txt`. The digamma file retains its copyright and author notice: Copyright (c) 2026 Robby Sneiderman; Authors: Robby Sneiderman. Other available upstream notices and headers are preserved in retained files or recorded source snapshots.

The current mathlib pin is `065356127b1dc0016f66b7283ce0ce2c4055aa55`; its Apache 2.0 license is preserved in `Mathlib-Apache-2.0.txt`.

This isolated port changes upstream files by extracting the needed declarations, replacing imports, removing blueprint metadata and unrelated dependencies, adapting Lean 4.34.1/mathlib APIs, and removing deprecated syntax warnings. Local cutoff, coefficient, error, and actual-zeta assembly proofs were added. Portable source records are included in the parent directory; source revisions and hash qualifications are described in the repository PROVENANCE.md. These changes are not represented as upstream releases or upstream endorsements.
