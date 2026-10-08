# Verification and reproduction

The package contains 466 Lean source and verification files.
[PROOF_SOURCE_HASHES.json](PROOF_SOURCE_HASHES.json) records both their current
SHA-256 values and the previously verified source hashes. This copy changes
comments in 19 Lean files; 447 files remain byte-identical. An exact comparison
after removing comments confirms that all non-comment Lean source is unchanged.
Fresh checks of this package are recorded in the accompanying source-bound
verification receipts. Those receipts identify the exact package and source
hashes; the historical checks below remain separately identified.
The 460 local modules include 456 production modules and four support modules.
The production proofs contain no admitted theorem, custom axiom or `sorry`.
`Challenge.lean` has two intentional specification holes and is not imported
by production proofs.

Checks completed on the previously verified source snapshot:

- A fresh Lean 4.35.0-rc2 build of all 460 local modules.
- Literal semantic contracts for the actual zero count, analytic multiplicity
  and moment, and separate-environment equality of both public Challenge and
  Solution types.
- Runtime inventory of 5,732 production declarations and replay of the complete
  73,216-declaration closure of all 5,731 safe production roots. Compiler
  auxiliaries are excluded as roots and rejected if reached by a logical proof.
- Direct Lean, NanoDa and con-ron checks of the Solution export.
- Official source-bound sandboxed Comparator acceptance, with source builds,
  fresh exports and NanoDa/Lean kernel acceptance, without an export substitution
  or sandbox bypass.
- A separate literal Type I contract and fresh empty-environment replay of its
  57,437-declaration closure.

The checked closures use only `propext`, `Classical.choice` and `Quot.sound`.
[CHECK_RESULTS.json](CHECK_RESULTS.json) records the exact compiler/pins and
check scope. Documentation, portable attribution and comment-only edits were
prepared separately from the proof checks. The historical check results apply
to the recorded prior source snapshot.

The compiler revision is `11acb17ec6b07a8f9e9173e6845197929540936b`.
All package pins are in [lake-manifest.json](../lean/lake-manifest.json).
Existing dependency caches were used. Their correspondence with the pinned
sources was not independently established by a complete dependency rebuild;
kernel replay verifies loaded declarations rather than that correspondence.

## Reproduce the proof checks

With the pinned toolchain and dependencies available:

```sh
cd lean
lake build MathCollab Solution
```

For an isolated fresh source build, independent contracts, runtime inventory
and complete production-root replay, use `scripts/verify.py --help`. Supply
`--lean` with the installed Lean executable, `--packages` with the matching
prebuilt Lake packages, and a new `--output` directory outside this repository.
`--direct-kernels` uses the installed sibling checker binaries. This script
does not install software or download dependencies.

The literal specification and proof are [Challenge.lean](../lean/Challenge.lean)
and [Solution.lean](../lean/Solution.lean); the selected names are in
[comparator.json](../lean/comparator.json). No hosted workflow is included or
automatically dispatched, and GitHub publication is not a Palomar submission.
