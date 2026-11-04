# Cumulative continuation: contextual and quotient-certificate effectivity

Branch: `formalization/cumulative-continuation-2026-11-03`.

Continuation base: `9dc34731f0438de2c726d93ca7a4eca7313490a2` (`9dc3473`), the accepted original root-checker checkpoint.

Accepted at: `2026-11-04T04:25:57.403133+00:00`.

The complete original **`numericStepTest` is primitive recursive jointly in
the binder context `Gamma`**, both finite windows, the complete finite Boolean
precedence table and the natural source, target and certificate inputs. The
original **`numericEdgeTest`, `pathTest` and `positivePathTest` are also primitive
recursive at each fixed ambient context**, together with the original
path-certificate decoder.

This continuation adds **27 fixed targets in 7 supporting components**.
Together with the preceding root-checker checkpoint, the cumulative branch now
records **46 fixed targets in 13 new supporting components**.
The earlier external and intervening local ledgers remain separate inherited
evidence; they are not counted again in these totals.

## New accepted components

| Component | Fixed targets | Result |
|---|---:|---|
| [NumberedUniformPackedDecoding](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedUniformPackedDecodingTargets.lean) | 6 | Exact raw structural, numeric and source-universe decoding, with primitive recursion joint in the context. |
| [NumberedUniformMultiset](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedUniformMultisetTargets.lean) | 4 | Context-uniform original certificate decoding and exact raw multiset checking, preserving every occurrence and witness. |
| [NumberedUniformMul](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedUniformMulTargets.lean) | 4 | Exact original Mul-selector calibration and primitive recursion with the context, windows and data varying jointly. |
| [NumberedUniformSelector](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedUniformSelectorTargets.lean) | 2 | The original unguarded decoded selector, including all Direct, Select, Copy and Mul cases, computes uniformly in the context. |
| [NumberedFocusCode](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedFocusCodeTargets.lean) | 5 | Exact original focus, dependent replacement and failure calibration, with both raw computations primitive recursive. |
| [NumberedNumericStepPrimrec](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedNumericStepPrimrecTargets.lean) | 2 | Exact typed contextual calibration and primitive recursion of the unchanged complete numericStepTest, joint in Gamma. |
| [NumberedQuotientCertificatesPrimrec](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedQuotientCertificatesPrimrecTargets.lean) | 4 | The original numericEdgeTest, path-certificate decoder, pathTest and positivePathTest are primitive recursive at each fixed ambient context. |

## Exact scope and context uniformity

Finite signature size `n` and arity remain explicit fixed parameters. For the
complete numeric step checker, `Gamma` is an input to a single primitive
recursive computation. Raw structural, numeric and universe decoders,
multiset certificate decoding, selector evaluation, focus and replacement
provide the required computation at the changing `focus.holeGamma` beneath
lambdas. Their exact calibrations recover the existing dependent typed
operations and every original failure case. Uniformity is established by
these joint computations, rather than inferred from the earlier theorems for
each separately fixed context.

The quotient-edge and path results fix the ambient `Gamma` because they reuse
the accepted representative computation at that context. Both windows, the
finite Boolean precedence table and the stated endpoint/certificate data vary
jointly. Arbitrary and duplicate window lists, arbitrary tables, the empty
signature and malformed natural inputs are included wherever their exact
targets quantify over them. No closure, precedence, correctness or effectivity
premise is added to these targets.

The original numeric step checker retains its outer source-universe check,
typed target decoding and result-type equality. At a discovered hole, the
inner selector remains the original **unguarded** `selectorTest`. Its Direct,
Select, Copy and Mul branches, zero-payload rules, invalid-tag rejection,
positive-label conditions, selected occurrence and type/head/window guards
are unchanged. Replacement retains the original hole-type check and the
numeric equality of the fully plugged target.

Focus permits exactly the existing five position kinds: lambda body,
auxiliary application function, ordinary base argument, numbered base argument
and numbered extra argument. Lambda descent updates the binder context;
argument indices, annotations, extra-list order and untouched siblings are
preserved. The raw traversal and frame reconstruction are calibrated to the
actual `focus` and dependent `plug` operations, including failed paths.

Mul retains the original lambda-descending marking and all kept, removed and
inserted occurrences. Witness order, literal removed indices and mark labels,
repeated indices, out-of-range failure and permitted empty insertion survive
the raw presentation. No source-universe test is added to its selector leaf.

Quotient checking uses the original representative comparisons. Path checking
retains every ordered edge entry and the final endpoint equality.
**`positivePathTest` rejects an empty path even when the endpoints coincide**,
preserving the source's positive closure `R = H⁺`.

## Source register

The whole-source register remains **154 checked, 2 inherited and 33 pending
out of 189**. This checkpoint adds **seven primary component links** to
`lem:id1` and **seven reuse links** to `lem:simulation`, with dependency summaries
updated to reflect the accepted contextual and quotient-certificate results.
Both complete source labels remain pending. Prior source statuses, accepted
declarations, frozen comparators and recorded source issues are preserved.

The source-register progress record identifies the completed computational
dependencies and retains the ordinary arithmetic representation, required
parameter interfaces, whole-source assembly and internal ID1 obligations.
No source statement is promoted solely because its supporting checker is
primitive recursive.

## Verification and preservation

All **7 exact component gates** and the **27-declaration focused aggregate**
passed the bounded serialized checker. Definitions and Targets were compiled
and their hashes frozen before candidate proof authoring; all frozen hashes
remain unchanged. Every audited axiom closure is contained in `propext`,
`Classical.choice` and `Quot.sound`.

The aggregate is `LogicLineages.CumulativeCheckpoint20261103ContextualEffectivity`. Its verified local source closure contains
**599 modules**, including **37 new Lean files** owned by this
checkpoint. Its accepted aggregate check took 1.221 seconds
with peak observed process-tree RSS 1,143,888 KiB after its suppliers
had been checked. Exact source hashes, compiler receipts and individual axiom
closures are preserved in the acceptance record.

The runner retains one thread, a 2048 MiB Lean heap, a 1536 MiB RSS ceiling,
a 2048 MiB free-memory floor and per-module 90-second CPU / 180-second wall
limits, using the pinned upstream cache. This is acceptance of the new gates
and focused aggregate, not a claim of a fresh full-root build or GitHub CI run.
The manuscript and original operation/certificate definitions remain unchanged.

## Next mathematical obligations

The next supplier is a genuine ordinary arithmetic graph representation for
the existing primitive recursive programs, followed by exact specialization
to the unchanged typedness, quotient edge `H`, positive closure `R` and direct
multiset replacement relations. The existing semantic certificate
equivalences connect accepted checker graphs to those relations after
existentially quantifying their actual certificates. A formula language with
semantic checker or relation atoms would not discharge this obligation.

The source-required parameter interfaces and whole-source simulation must
still be assembled, retaining one source window `S = Ty(s)` for both endpoint
representatives. The present fixed-context edge/path result does not by itself
supply a formula compiler uniform in every possible context.

Internal ID1 accessibility remains a separate proof: actual positive
arithmetic operators and computability clauses must be expressed in the formal
language and the source's required derivations constructed. External primitive
recursiveness and standard-natural-number graph correctness do not establish
that derivation. The later norm-extraction and ordinal suppliers also remain
separate. The previously recorded source obstructions are unchanged.

## Evidence and prior checkpoint

- [Accepted exact targets, hashes, compiler receipts and axiom closures](CONTEXTUAL-EFFECTIVITY-ACCEPTED.json)
- [Specifications frozen before candidate authoring](CONTEXTUAL-EFFECTIVITY-FREEZE.json)
- [Source-register dependency progress and seven primary/seven reuse links](SOURCE-REGISTER-PROGRESS.json)
- [Verified focused local source closure](SOURCE-CLOSURE.json)
- [Next ordinary arithmetic graph bridge and internal ID1 boundary](NEXT-ARITHMETIC-BRIDGE.md)
- [Prior root-checker checkpoint and inherited scope](../STATUS.md)
- [Prior root-checker acceptance record](../termination-ordering/ROOT-EFFECTIVITY-ACCEPTED.json)
