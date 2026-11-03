# Confined original comparison in the exact source type window

Source: paper06 `lem:simulation`, lines625–657 of `06-godel-t-termination-ordering/paper.tex`, especially the fixed universe `S = Ty(s)` in the statement and the final confinement clause. The source SHA-256 is `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`. The quotient and its positive closure are specified immediately before `lem:id1`, at lines551–556.

The sole comparison premise is the existing `LiteralContexts.ConfinedStrict above s t` on actual ordinary source terms at their original shared context and type. Its definition already combines the original strict recursive derivation with `typeSupport t ⊆ typeSupport s`. This component does not add endpoint confinement, subtype closure, normality, a chosen simulation certificate, or a precedence assumption.

`sourceWindow s` is exactly `Source.SourcePortContexts.literalTypes s`. It contains no target-dependent contribution. The accepted literal enumeration theorem identifies its membership with the original source type support. The symbol window is the existing complete finite list `NumberedOrdinaryWindow.symbols n`. Every finite signature, actual arity function, original context and result type remains quantified, including the empty signature.

The first target derives subtype closure and both original `OriginalGood` and translated `InUniverse` endpoint conditions in this same source window. Target confinement must come from the original confined-comparison support inclusion. The second target requires a genuine positive-count `WindowTrace` between the unchanged `translated s` and `translated t`, with `allBoundaries` in this source window. The third requires a positive path for the unchanged `NumberedQuotientPaths.QuotientEdge` between the actual `representativeCode` values of these translations, still in the same source window and context. It is not a path on raw codes, a supplied quotient relation, or a zero-step equivalence witness.

These are the source-window and relational simulation clauses. They do not establish numerical computability of the source translation or least-code representative, arithmetic representation of the actual edge/path relation, an internal ID1 accessibility proof, the Bachmann–Howard bound, or the whole numbered `lem:simulation`. The accepted source comparison, restricted reduction, finite primary class and least-code representatives remain unchanged, including the separately recorded local transitivity obstruction.

## Exact targets

- `ActualSourceWindow`: source-only subtype closure and original/translated endpoint confinement.
- `ActualStrictWindowTrace`: a positive actual restricted trace with every boundary confined.
- `ActualStrictQuotientPath`: the actual positive least-code quotient path.

## Files

- [Definitions](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedConfinedSourceSimulationDefinitions.lean)
- [Exact targets](../../../LogicLineages/OrdinalComparison/TerminationOrdering/NumberedConfinedSourceSimulationTargets.lean)

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](CLASS-CANDIDATES-FREEZE.json) and
[the acceptance record](CLASS-CANDIDATES-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
