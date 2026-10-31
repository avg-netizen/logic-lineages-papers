# Collection verification

The collection was prepared 28 October 2026; the foundations source repair
was integrated and separately rebuilt on 30 October. All six manuscripts passed clean builds after
copying the collection into a fresh temporary directory, without private
research files. Each was built with its own `python3 build_pdf.py` using
Tectonic's `--untrusted --keep-logs --only-cached` options. The delivered PDFs
were checked against those isolated builds. The current foundations PDF was
rebuilt after its source repair; its six included inputs also pass in a fresh
isolated directory. The five other manuscripts retain their 28 October checks.

| Manuscript | Pages | Theorem / lemma / proposition / corollary statements |
|---|---:|---:|
| Foundations and guide | 19 | 18 |
| Gödel-T termination ordering | 14 | 24 |
| Equality and one variable | 16 | 21 |
| Multivariate comparison | 19 | 18 |
| Actual-source expressivity | 15 | 21 |
| Descent and modular counts | 11 | 15 |
| Total | 94 | 117 |

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

The foundations now fixes every binary expansion and padding convention.
Its Appendix A proves the weak scalar inequality, graded domain and original
bounded-norm multiplier and exhibits the 204/184 closed-source distinction
between two policies. Its translation is policy-relative; these additions do
not assert a convention-independent original assignment or a new solution of
the full comparison problem. The bounded witness control and full same-model
review are included in that manuscript's repair directory.

The proofs were checked collaboratively during consolidation, including the
source-observer and ground-binder arguments, the functional-input reduction,
the control-perturbation reduction, shared-variable and type/control domains,
and the distinction between complete scalar observations and full-state periods.
The published background remains cited background. This is an AI-assisted
hand-proof collection for mathematical review, without proof-assistant
certification, independent human audit or an established-priority claim.
The remaining standard-control all-ground comparison problem is explicitly
open in the papers.
