# Independent review — dependency ordering orchestration

Decision: **accept the portable dependency-ordering helper** on 2026-11-17.
It changes the order of explicit inputs to the unchanged native checker;
it does not replace native checking or relax its validation requirements.

## Reviewed pins

- `ordered_check.py`: `715e254125711878682b8e2bfad0a1f8dc1d6bd23ca8b8eda3652bc1b3bf8714`.
- `scripts/check.py`: `fefa8d645edc1c7bd1e4abc750cfaa6556adfc6cc80d6aecaff952192322a144`.
- `verification/continuation-2026-11-13/bounded-evidence-verifier/verify_evidence_bounded.py`: `04bfb9d21762122b76b65f8eb4600fe925d1c75b6b3b6c5bb82358dba0683bff`.

The helper derives the formalization root from its location. Before importing
either existing supplier it checks that supplier's exact SHA256. Its
comment-stripping supplier is byte-for-byte the same algorithm used by the
unchanged checker's scanner; the helper uses the checker's own `source_for`
and import regex.

## Scheduling and validation equivalence

The iterative DFS records a local module after its dependencies, rejects
active import cycles, and deduplicates completed modules. Every requested
root is checked for an existing local source before traversal. The final
ordering is supplied as explicit module arguments to the unchanged
`checker.main()`. Consequently that checker's recursive scanner encounters
already-visited dependencies and avoids the Python recursion-depth failure
of the long source-supplier chain.

All local modules are still scanned by the original checker, including its
forbidden-placeholder and added-axiom checks. The checker still identifies
the pinned compiler and imported objects, validates cache provenance, owns
the shared locks, enforces the local stop policy, applies the free-memory
floor, compiles in one-worker order, and emits the original native receipts.
The wrapper passes heap 2048 MiB, process-tree RSS 1536 MiB, and free floor
2048 MiB explicitly. The pinned checker's unchanged defaults are 90 CPU
seconds, 180 wall seconds, and one worker. No proof source, original checker,
toolchain pin, resource ceiling, or source theorem is modified.

The receipt's `requested` list now contains the ordered local closure instead
of only the endpoint root. The helper prints the original requested roots
and closure summary separately as `FOCUSED_CLOSURE`; this summary must be
retained with the native log for review. `--list` is only a read-only closure
summary and does not constitute proof acceptance.

## Independent read-only checks

The reviewer imported the helper without calling its `main` and inspected
only local sources. For both small endpoints, the iterative module order
and external import set equal the existing recursive evidence verifier's
results exactly:

| Exact endpoint | Local modules | Order/external-set match |
| --- | ---: | --- |
| `RawApplicationDynamics.StatementChecks` | 23 | Yes |
| `LiteralCommonKnowledgeCounterexample.StatementChecks` | 300 | Yes |

The installed-source endpoint has 2,905 unique local modules; the union of
all three endpoints has 2,927. In both closures, every local dependency
appears strictly before its consumer, every requested endpoint is present,
and there are no duplicate module entries. A mixed valid-plus-missing-root
request raises the intended `ValueError` before checking.

The earlier scratch helper, SHA256
`1ccd8bc13855f7eb0e92edb1e295746cfccff3af1c9e8a7fb2074cfd85b1dea6`,
did not reject missing requested roots separately. Its current native run
requested the existing exact `SameSourceOriginalAdoption.Proof` module,
so that omission does not affect that run. The saved portable helper adds
the required root validation and pins its immutable suppliers.

This orchestration is compatible with the existing source and verification
constraints. It does not turn a conditional source consumer into an
unconditional theorem or establish a full-root build. Exact endpoint,
source-hash, receipt/log, and standard-axiom acceptance still require the
coordinator's successful native gates. This reviewer ran no native compiler
or Git operation.

## Quiescent evidence invocation

The separately prepared scratch `verify_application_literal.py` was reviewed
at SHA256 `599415b98cd0bc7f7eb2adca1894bbe84b7e8c486b3aae9e891c07a873bd1d61`.
Its read-only preview has SHA256
`b67747e76acfffd4ab8c18f242f8263edc9401517e74f1bdd598fc77de649885`.
This invocation is accepted for the final quiescent evidence check.

The script obtains the exact three-gate closure from the reviewed portable
helper, then supplies fourteen modules from that closure as earlier roots
before the three final gates. Those anchors reduce recursion depth in the
unchanged evidence verifier. The script asserts equal local-module sets and
counts and equal external-import sets before invoking `verifier.main()`.
All six exact aliases remain explicitly required. The baseline commit and
frozen-file checks remain enabled; allowed inherited paths are the aggregate
import file, the existing handoff, and the verifier's existing AGENTS default.
No inherited mathematical source is newly exempted.

An independent `--list` evaluation reproduced the preview exactly: 2,927
modules, fourteen anchors, three final gates and six exact aliases. Every
anchor is in the final closure, and local/external sets are equal. The anchor
traversal changes the relative order of some independent modules, not the
module set, per-module dependency map, native-receipt selection, or validation
conditions. The verifier's receipt selection order is independently fixed by
sorted receipt path and module-row order.

The only verifier global changed by the wrapper is `HERE`, to place output
under `.lake/application-literal-evidence`. Inspection shows that after
module initialization, `HERE` is used only to choose the evidence output
directory; `ROOT`, source lookup, frozen checks, native receipts, original
verifier hash and validation logic remain unchanged. The intended final
roots and expanded original arguments are preserved separately in
`EVIDENCE-INVOCATION.json`. The invocation record and wrapper pins should
accompany the resulting snapshot because its `gate_roots` includes the
ordering anchors. Neither the native compiler nor the full evidence verifier
was called by this independent review.
