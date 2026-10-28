# Collection verification

Prepared 28 October 2026. All six manuscripts passed clean builds after
copying the collection into a fresh temporary directory, without private
research files. Each was built with its own `python3 build_pdf.py` using
Tectonic's `--untrusted --keep-logs --only-cached` options. The delivered PDFs
are the outputs of those isolated builds.

| Manuscript | Pages | Theorem / lemma / proposition / corollary statements |
|---|---:|---:|
| Foundations and guide | 13 | 13 |
| Gödel-T termination ordering | 14 | 24 |
| Equality and one variable | 16 | 21 |
| Multivariate comparison | 19 | 18 |
| Actual-source expressivity | 15 | 21 |
| Descent and modular counts | 11 | 15 |
| Total | 88 | 112 |

These are mechanical counts of numbered result environments, not a measure of
significance or an imposed writing target. Definitions, problems and examples
are excluded from the result total. Immediate corollaries may share the
preceding proof instead of having a separate proof environment.

The final checks establish:

- Every TeX input is included and every citation, label and local companion
  link resolves. Labels are unique and unused bibliography entries were removed.
- The TeX logs have no unresolved-reference, missing-character or overfull-box
  warning. Underfull bibliography notices can remain.
- All PDF fonts are embedded. They use Computer Modern and AMS; the one-variable
  paper also uses Computer Modern Super for a standard text symbol.
- PDF text extraction succeeds. Representative title and technical pages were
  rendered and inspected for formula placement, margins and legibility.
- Public folders and manuscripts use descriptive mathematical names, with no
  private problem labels or unavailable proof-file paths. Origin fingerprints
  are descriptive metadata rather than proof dependencies.

Exact source/PDF SHA-256 digests, font tables, page counts and per-paper
checks are in [COMPARISON-CHECKS.json](COMPARISON-CHECKS.json); repository
file digests are in [SHA256SUMS](SHA256SUMS). Individual preparation records
are included in the manuscript directories.

The proofs were checked collaboratively during consolidation, including the
source-observer and ground-binder arguments, the functional-input reduction,
the control-perturbation reduction, shared-variable and type/control domains,
and the distinction between complete scalar observations and full-state periods.
The published background remains cited background. This is an AI-assisted
hand-proof collection for mathematical review, without proof-assistant
certification, independent human audit or an established-priority claim.
The remaining standard-control all-ground comparison problem is explicitly
open in the papers.
