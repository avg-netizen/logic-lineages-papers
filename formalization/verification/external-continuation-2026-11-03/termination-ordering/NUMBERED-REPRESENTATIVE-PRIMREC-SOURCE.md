# Effectivity of the actual least-code representative

Source: paper06, `06-godel-t-termination-ordering/paper.tex`, lines551–556, immediately before `lem:id1`: finite computable primary classes and their least-code representatives, followed by the induced one-step relation H and its positive closure R. The source SHA-256 is `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`. This component supports the numeric translation in `lem:simulation` and the canonical arithmetic carrier needed by `lem:id1`.

The target is the existing `NumberedLeastCodeRepresentative.representativeCode`, defined as the minimum of the original finite `primaryClass` after its image under the existing injective `packedNumber`. Neither that class nor its reachability depth, edge test, numeric encoding or minimum is replaced. The existing packed `Primcodable` instance comes from the accepted literal numeric codec and normalization theorem; no new presentation makes the representative computation primitive by definition.

The auxiliary Boolean `classNumberTest` decodes a natural with the actual `decodePackedNumber` and then invokes the original `primaryTest`. It uses no universe filter. This distinction preserves the original behavior on arbitrary windows: `vertices` inserts the initial term even when that term lies outside the supplied window, and every stage of `reachable` contains it. The equality between this Boolean and membership in the original numeric class therefore uses the literal decoder roundtrip and numeric soundness, rather than the conditional semantic theorem identifying primary-class membership with `WindowPrimary`.

The bounded search scans `List.range (packedNumber q + 1)` with this exact Boolean and returns `findIdx`. Since that range lists each natural in ascending order, the first successful index is the first successful code. The initial term itself supplies a successful test within this range, and the original minimum is at most its code. Exact calibration must identify the result with the existing `representativeCode` for all inputs. It may not add `SubtypeClosed S`, endpoint `InUniverse`, source normality, a supplied class bound, a representative witness or a computability premise.

All four targets quantify every finite signature size, actual arity function and original context. The primitive-recursion targets fix those parameters outside `Primrec`, as required by the dependent packed output representation, and vary the symbol list and type list jointly with the packed term or natural input. Empty or duplicate window lists, malformed natural codes and out-of-window packed terms remain in scope. No joint effectivity in the dependent context or signature parameters is claimed.

The final target concerns the unchanged `canonicalCarrierTest`: its original `decodeUniverse` rejects malformed or out-of-window inputs, and on a successful decode it compares the actual representative code with the original input natural. This remains a Boolean computation target even on windows for which the separate semantic canonical-carrier theorem requires subtype closure.

## Exact targets

- `ActualRepresentativeBound`: the existing representative is at most the original packed number, unconditionally.
- `ActualBoundedRepresentativeCalibration`: the explicit bounded numeric search equals the existing representative on every input.
- `ActualRepresentativePrimitive`: the actual representative function is primitive recursive jointly in both windows and the actual packed term.
- `ActualCanonicalCarrierPrimitive`: the actual canonical-carrier Boolean is primitive recursive jointly in both windows and every natural input.

These are computation and calibration suppliers. They do not assert an arithmetic formula for H or R, effectivity of a numeric source translation or complete reduction/path checker, an internal ID1 accessibility proof, the Bachmann–Howard bound, or completion of either whole source lemma. No source comparison, equivalence or reduction rule is changed.

## Files

- [Definitions](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedRepresentativePrimrecDefinitions.lean)
- [Exact targets](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedRepresentativePrimrecTargets.lean)

## Accepted verification

The fixed statement gate and the thirteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](PRIMARY-CLASS-PRIMREC-FREEZE.json) and
[the acceptance record](PRIMARY-CLASS-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
