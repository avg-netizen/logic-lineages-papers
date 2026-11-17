# Exact recursive supplier congruence audit

Read-only audit, 2026-11-17. No new theorem, native run, reflection, or count.
Namespace prefix below: SourceComputabilityCompletion.

## Finding

No existing generic internal termCheck/TermAccepted member-supplier congruence was found in the inspected decoder, internal acceptance, transport, and graph-congruence sources. Existing OriginalUniverseDecoderTransportInductionProof.allRawTransport changes raw/context coordinates but retains the identical M and W; it cannot be instantiated to change M. Native pointwise evaluation equality is not an internal graph bridge.

The proposed explicit p† member lift is sufficient at the coordinate level: set lift M = composition M [projection 0, leftOf(projection 1)], p†.base.member = lift M0, and W = W0 literally. A proved arbitrary-output internal iff between contextMember(lift M0)(type,c) and M0(type,c) would cover every recursive query, not only the root. This audit does not claim that adapter has already been proved.

## Minimal useful target

For the SAME arbitrary H and W and two arbitrary M,N, derive an internal implication between original TermAccepted H M W typ raw gamma c and TermAccepted H N W typ raw gamma c from internal success inclusion of the member suppliers at this fixed outer c:

    forall type, graph2 M 1 type c -> graph2 N 1 type c.

Prove the corresponding ArgumentsAccepted implication simultaneously. Swap M,N for the reverse direction, then assemble object-language iff. A concrete unconditional endpoint for contextMember(lift M0) versus M0 must discharge this internal inclusion from the adapter, not expose it as an unexplained source-interface premise. Arbitrary-output adapter equivalence is stronger than needed: acceptance-only output 1 transfer suffices for this recurrence route. No Code, ArrowClosed, native calibration, term-validity, equal-cutoff, or child-acceptance premise is needed in the generic claim.

This is acceptance graph congruence, not yet arbitrary-output equality of termCheck. Do not label it all-output graph congruence without separately using/proving original checker Booleanity and rejection transport.

## Why every recursive coordinate is covered

OriginalUniverseDecoderDefinitions:
- memberAt M type = composition M [type,context]; context is projection 1 of [request,outerContext].
- guard queries M(requested type,c) in term mode, and extraGuard queries M(lambda domain,c) at tag 1.
- termRun/argumentsRun pass their fourth input c into iterate; iterate's recursive step passes projection 3 unchanged to transition.
- Gamma is encoded in requests and changes at lambda, but is never the second argument of M. The original outer c stays invariant.

Concrete accepting recurrences confirm:
- Variable/bottom: M(typ,c).
- Lambda: M(typ,c), M(domain,c), then child at codomain and extended Gamma, SAME c.
- Application: M(typ,c), children at arrow(domain,typ) and domain, SAME c.
- Ordinary head: M(typ,c), W(head,c), argument-list recursion at head type-list and SAME c.
- Numbered head: M(typ,c), W(head,c), two argument recursions at baseTypes and extraTypes, SAME c; retain recorded/requested equality and original lack of head-result/requested equality.
- Nil: no M query.
- Cons: term child at domain, argument tail at tailTypes, SAME c.

Thus a bridge merely at the original root typ is insufficient, but a bridge for arbitrary type and fixed c (uniform under binder renaming/weakening) is sufficient. The p† adapter proposed by iteration_plan has exactly the stronger arbitrary type/context coverage. No recursive member query uses pair(c,gamma), a changed context, or a synthesized type restriction outside that coverage.

## Existing exact recurrence suppliers

Use OriginalUniverseDecoderInternalAcceptanceLeafProof.variableIff, bottomIff, nilIff; OriginalUniverseDecoderInternalAcceptanceUnaryProof.lambdaIff, ordinaryIff; OriginalUniverseDecoderInternalAcceptanceBinaryProof.applicationIff, numberedIff, consIff. Their frozen propositions are recorded in OriginalUniverseDecoderInternalAcceptanceTargets. Each is bidirectional at the literal original term/arguments checker and raw+1 fuel, so reconstruction introduces the real target graph, not an abstract accepted predicate.

Use OriginalUniverseDecoderTransportRejectedProof.termForbidden/termSix/termSeven/argumentsForbidden/argumentsOther/unknown for wrong modes and unknown tags. These work with either member supplier and arbitrary conclusion from source acceptance contradiction.

OriginalUniverseDecoderTransportInductionProof.transportStep/allRawTransport provide an inspected template: exhaustive rawTagCases, actual selector queries, original smaller-child strong induction, arbitrary request/context/type binders, both modes. OriginalUniverseDecoderTransportBindingProof.rawInduction/belowRawApply are specialized to its fixed Transport formula, so reuse their proof design and underlying InternalStrongInduction APIs, not their conclusion as if parameterized by a new predicate.

## Resource-friendly implementation decomposition (not started)

1. Definitions and rename/binding helpers for a new small AtRaw: universally bind requested type/list and Gamma; fixed c may remain a free parameter with its supplier inclusion in Delta. Conjoin term-mode and argument-mode implications. Alternatively quantify c and put its inclusion inside the implication. Ensure induction renaming preserves inclusion.
2. Leaf cases variable/bottom/nil and invalid modes. Eliminate the exact source recurrence, transfer M hits, introduce exact target recurrence.
3. Lambda and ordinary cases separately. Query actual payload/head fields once; preserve all equalities/H/W observations. Obtain only actual smaller original child obligations; no transformed-raw budget issue.
4. Application, numbered, cons cases separately. Reuse the actual original child-code descent arithmetic used by transport. Both term and argument IHs required.
5. Exhaustive tag dispatch and strong raw induction. Source successful acceptance supplies actual recursive successes by recurrence elimination. No inverse enumeration required.
6. Reverse implication by swapped supplier equivalence and object-language iff assembly. Then instantiate the internally proved p† adapter and literal W0; sourceEquation can consume resulting TermAccepted transport.

This avoids reopening machine-run/fuel proofs. A direct machine proof is possible in principle (guard equality, transition equality, symbolic-count iteration equality, finish), but would need an additional generic internal recursion-congruence proof and all-output supplier handling. The already checked bidirectional acceptance recurrences make source-raw induction the smaller evidenced route.

## Remaining boundaries

Even after this congruence, selected source success additionally needs actual G(c), packed input/parameter pairs, and sourceEquation. It does not prove the independent finite Program1 p.window condition, sidecar activity, sidecar C equality with the initial representative, or final accessibility. The explicit p† selection is a new honest concrete input choice, not replacement of an arbitrary p by native calibration. No work on those claims or compiler work was performed in this audit.
