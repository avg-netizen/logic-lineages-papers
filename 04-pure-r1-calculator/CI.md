# Public Lean compilation

[![Pure R1 Lean verification](https://github.com/avg-netizen/logic-lineages-papers/actions/workflows/pure-r1-lean.yml/badge.svg?branch=main)](https://github.com/avg-netizen/logic-lineages-papers/actions/workflows/pure-r1-lean.yml)

The [workflow](../.github/workflows/pure-r1-lean.yml) runs on pushes to `main`,
pull requests and manual dispatch. Its public run page identifies the exact
commit, steps and result.

Each run starts on a fresh GitHub-hosted Ubuntu runner. It installs the toolchain
from `lean/lean-toolchain`, acquires the public Mathlib cache for the committed
dependency revisions, and checks that the Lake files were not changed. It also
checks every dependency's actual Git revision and rejects any pre-existing local
calculator `.olean` files. No calculator build objects are restored from a cache.

The job then runs `python3 scripts/verify.py --lean`: all local Lean modules
compile from source in import order, the principal axiom reports are checked,
and the Python tests and explicit fixtures run. The
[statement checks](lean/R1Calculator/StatementChecks.lean) require the exported
endpoint, Sigma-one checker and greatest-endpoint results to have their explicit
unconditional types. They also check the numeric norm bound and sharpness.

The accepted reported dependencies are only the standard `propext`,
`Classical.choice` and `Quot.sound`. The verifier rejects proof holes, added
axioms, `native_decide` proofs and missing reports for the core conclusions.

Each successful run publishes a summary and a downloadable artifact containing
the complete compile/test log, fresh `VERIFICATION.json`, source hashes, exact
dependency revisions and run provenance. Artifacts are retained for 90 days;
the workflow/run pages provide the public compilation result.

This job verifies the Lean development and tests Python separately. It does not
claim formal verification of Python or rebuild the manuscript PDF; the paper's
local build record is documented in [VERIFICATION.md](VERIFICATION.md).
