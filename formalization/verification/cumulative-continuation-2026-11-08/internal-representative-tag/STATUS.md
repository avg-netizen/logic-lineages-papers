# Original representative outer tags: exact gate passed

Four supporting targets are checked at their unchanged frozen types:

1. The ORIGINAL least representative has the input packed term's original
   numeric outer type, for every finite window and every packed term. No
   subtype-closure or universe-membership premise is required.
2. Concrete source and target representative wrappers preserve the complete
   existing all-input calibration, including decode failures and zero defaults.
   The source keeps its universe filter; the target uses packed decoding alone.
3. Under actual validity and wrapper-output graphs, independently supplied raw
   and representative outer-tag graph outputs are internally equal.
4. A representative OUTPUT outer-tag graph internally yields the RAW INPUT
   outer-tag graph at the same symbolic tag, with no supplied raw-tag witness.
   The converse is checked as well.

The wrapper is the literal Program AST that checks the shared validity leaf
for output exactly one, then pairs the raw input's left field with the old
representative's right field; on rejection it returns zero. withRepresentatives
reuses InternalOriginalStepGuard.Data.sourceValid and targetValid and preserves
the old stepProgram literally. There are no correctness or derivability fields.

The arbitrary-window semantic proof uses the original fixed-type candidate
enumeration, reachableBound and the attained minimum of classNumbers. It does
not apply subtype-closed primary-equivalence correctness outside its domain.
Both internal graph targets work for arbitrary Program leaves, positive bodies
and symbolic terms, without external calibration or a reflection principle.
The helper rules work under arbitrary ambient hypotheses. The backward tag
rule obtains the intermediate field from the actual composition graph and
identifies it through internal pairing inverse and graph functionality.

This is the representative part of the canonical-vertex-to-raw-source bridge.
It does not provide a canonical typed-carrier entry rule or representative
application congruence. Explicit selected edge/checker assembly, typed argument
and endpoint guards, application-validity transport, context-uniform/joint-Gamma
assembly, malformed pathValue handling, CertifiedApplicationLift and the
remaining constructor/multiset/lambda/substitution/fundamental ID1 arguments
remain outside this packet. No numbered source statement is promoted.

## Acceptance

All four exact comparator aliases and public target axiom closures passed with
only propext, Classical.choice and Quot.sound. Namespace audits checked every
one of the 17 new proof/helper declarations: six evaluation theorems, seven
internal support theorems and four public aliases.

All 1,054 local modules in the focused import closure have successful native
receipts matching their current source hashes, including public meta imports.
All 43 frozen specification, prerequisite, correspondence and paper pins are
unchanged. Independent specification review and native preflight preceded
proof authorship. SOURCE-CORRESPONDENCE.md remains the original pre-proof freeze
snapshot; this status and ACCEPTANCE.json record the subsequent acceptance.

The serialized resource profile is unchanged: 2,048 MiB heap, 1,536 MiB process
tree RSS, 2,048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall
seconds per module, using only the existing upstream cache. The packet peak
successful RSS was 1,056,876 KiB; the source-matched receipt closure peak was
1,176,760 KiB. No full-root build or remote-CI result is claimed.

One local compiler repair made a dependent packed-term projection explicit in
the candidate-type proof. The failure log, receipt and source snapshot remain
local. No frozen type, existing supplier, resource profile or CI setting changed.
All owned checker sessions exited and were reaped; both shared compiler locks
were verified free, and the sole slot was released to the parent. This worker
and its proof author took no Git action.

## Portable packet

Seven accepted InternalRepresentativeTag Lean files: Definitions, Targets,
Preflight, EvaluationProof, SupportProof, Proof and StatementChecks. Five
portable evidence files: FROZEN-SOURCE-PINS.json, SOURCE-CORRESPONDENCE.md,
SOURCE-PINS.json, ACCEPTANCE.json and STATUS.md. The precise allowlist is in
ACCEPTANCE.json. Native logs, receipts, the failed snapshot and full closure
receipt mapping stay local and are not needed in the portable packet.

## Reproduction

    python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagStatementChecks
