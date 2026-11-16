# Original enumeration equation: resumed candidate

Status: **candidate; exact native gates and axiom audits pending**. This
handoff describes the unchanged `FULL02.json` draft preserved at branch head
`1144d37f04508af0b09ea3f6bb8b3007307f4228`. It does not accept that draft.
All fourteen packet source hashes match the preserved manifest. The three
frozen files and eight upstream provenance files also match their manifests.

## Source correspondence

`OriginalEnumerationRecursion.enumeration n` remains the literal selected
recursor over the original `R`, `D`, and `G n`. Its node is the encoded pair
`(variableBound, fuel)`, and `R` observes the fuel component. The raw node is
never substituted for its rank. At positive fuel, `D` retains the ordered
pair of calls at predecessor fuel: first the same variable bound, then the
successor variable bound. At zero fuel, `D` is empty. The parameter retains
the original codec `(types, (heads, (labels, tupleBound)))`.

`G n` uses the original constructor layer and the two original `getD` answer
positions with empty-list defaults. Its outer successor encodes `Some`; the
empty-list payload zero therefore remains `Some 0`, encoded as one. The new
`answerMap` is raw-list recursion over the same standalone program. It
preserves order, repeated children, and zero payloads.

## Frozen endpoints and proof route

| Frozen target | Candidate proof route | Premises retained at the endpoint |
| --- | --- | --- |
| `Targets.InternalPreviousAnswers` | Own-root agreement plus generic ordered-map transport in both directions. | The actual rank graph, the previous cache graph at that rank, and the original dependency-list graph. |
| `Targets.InternalEnumerationEquation` | Actual answers and cache agreement feed `ArgumentEntriesConsTable.FinalProof.finalAnswers` specialized to the same `R`, `D`, and `G n`; functionality proves both directions. | Only the graph of the original ordered answers; no supplied child results, validity, or recursive induction hypothesis. |

The supporting proof files make the missing cache facts internal:

1. `Extraction/RootProof` constructs the actual own-root singleton frontier
   and final singleton cache at successor observed rank, proves the combine
   result is `Some`, and relates selected extraction to cache lookup.
2. `Extraction/Proof` transports that lookup through the already specified
   cross-root cache coherence for this enumeration tuple. It preserves
   the complete tagged lookup value, including `Some 0`.
3. `ZeroProof` uses strict dependency-rank decrease to eliminate any child
   at observed rank zero. `ChildProof` uses the aligned extraction at the
   actual predecessor cache for positive rank.
4. `CoverageProof` binds the child and value quantifiers internally.
   `OwnProof` derives the required own-root lookup agreement without adding
   agreement, membership, or `Some` witnesses to the public target.
5. `Proof.previousAnswers` specializes generic raw-list ordered-map
   transport to this enumeration program. `EquationProof` obtains rank,
   cache, dependency, and combine witnesses through internal program
   totality; no native evaluation is used as an internal proof premise.
6. `Proof.exchangeEquation` exposes the two internal implication proofs
   as the required external equivalence of derivability. Reverse output
   transport cancels successor, preserving the option encoding.

## Native acceptance still required

Root owns the sole serialized compiler queue. Check the following modules
with `scripts/check.py` at the unchanged 2048 MiB heap, 1536 MiB RSS, and
2048 MiB minimum-free-memory profile:

1. `LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Preflight`
2. `LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.StatementChecks`

The existing statement-check file compares both declarations with the frozen
types and audits their namespaces. Each supporting proof namespace also has
an axiom audit. Native success, exact comparison, the standard-axiom closure,
and independent source review must all precede acceptance. Any elaboration
repair must preserve the frozen files and retain the failed source snapshot.

## Scope boundary

This packet concerns the literal internal recursive equation. It does not
establish enumeration completeness, `codeBounds` sufficiency, `classCodes`,
the full `Q` package, or paper06 source computability/accessibility. The
numbered register remains 175 checked, 2 inherited, and 12 pending out of
189; the accepted supporting-contract baseline remains 729. No new contract
is accepted by this candidate handoff.
