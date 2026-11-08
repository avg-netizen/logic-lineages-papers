# Internal parameterized application-path lift

Both frozen supporting targets passed on 8 November 2026, on the first complete
proof check. The definitions and targets retain their frozen hashes.

The original calculus proves preservation of reflexive and positive path
acceptance at arbitrary symbolic source, target, certificate, output and
parameter terms. The proof uses the exact existing application path-map AST,
whose inputs remain `[code, parameter, domain, codomain, RAWargument]`, and the
existing original edge-lift program. No new mapper or certificate encoding is
introduced. Every edge-checker call receives the same symbolic parameter.

The two local assumptions are internal single-edge invariant propagation and
single-edge application compatibility, with both actual vertex outputs and
the actual lifted edge certificate retained. Internal original list-code
induction derives the whole reflexive path rule. Positive acceptance excludes
zero in the calculus; total head/tail graphs then provide a genuine original
cons, whose reflexive suffix uses that induction. No whole-path assumption,
semantic decoding premise or fixed-parameter reflection is used.

The final receipt is `build-reports/1794179901817633961-5.json`.
Both exact aliases depend only on `propext`, `Classical.choice` and `Quot.sound`;
the 20 supporting and main theorem declarations also passed namespace axiom
audits. The serialized profile stayed at 2048 MiB heap, 1536 MiB process-tree
RSS and 2048 MiB minimum free memory. No frozen specification or prior accepted
source was edited.

Public exact exports are
`InternalParameterizedApplicationPathLiftProof.actualInternalParameterizedReflexivePathLift`
and
`InternalParameterizedApplicationPathLiftProof.actualInternalParameterizedPositivePathLift`.
The internal `allRows`, `rowApply`, `consLift` and `positiveConsCases` helpers
remain available for the concrete source assembly.

This packet closes the generic parameter-carrying path-induction step.
Concrete original local edge rules and outer object/context wrappers remain
separate obligations; no numbered source statement is promoted here.
