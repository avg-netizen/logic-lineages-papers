# Internal application path lifting

## Frozen scope

`InternalApplicationPathLiftDefinitions.lean` and
`InternalApplicationPathLiftTargets.lean` specify two generic internal targets:
`ActualInternalReflexivePathLift` and `ActualInternalPositivePathLift`. Their
hashes were frozen before candidate proof files existed. Acceptance status and
source hashes belong to the separate verification record.

Both targets quantify an arbitrary original positive inductive body, an edge
`Program 3`, a vertex `Program 5`, and an arithmetic-invariant `Program 5`.
They retain arbitrary object-language variable types, assumption contexts,
symbolic endpoints, raw certificate codes, and actual graph outputs. The four
unchanged parameters are the context code, domain code, codomain code, and
argument code. The map receives the raw certificate followed by these four
parameters.

The supplied contextual conjunction contains the invariant at the source,
acceptance by the original concrete path-checker AST, the two actual vertex
graphs, and the actual graph of `InternalApplicationPathMap.pathMap` at the
supplied mapped certificate. The conclusion is acceptance of that same mapped
certificate between those same supplied vertex outputs. The reflexive target
uses `checker edge false`; the positive target uses `checker edge true` and
retains its rejection of the empty certificate.

## Exact local premises

The two additional premises are families of closed derivations in the original
internal calculus. They are not assertions of standard-model truth.

`InvariantPreservation body edge invariant` supplies, for every parameter tuple
and every symbolic source, target, and certificate, a derivation of

```
invariantAt invariant ps x ∧ edgeGraph edge x y certificate
  → invariantAt invariant ps y.
```

Here `invariantAt` is exact-one acceptance of an arithmetic Program at the
unchanged five inputs. It can record the concrete typing, finite-window, and
argument requirements when the generic theorem is instantiated. The frozen
definition contains no computability predicate or path-closure premise.

`EdgeCompatibility body edge vertex invariant` supplies a closed derivation
that transforms one accepted edge. Its antecedent contains the source
invariant, the original edge acceptance, the actual vertex graph at each
endpoint, and the actual graph of the already explicit
`InternalApplicationCertificateConstructors.edgeLift` at the supplied lifted
edge certificate. Its conclusion is acceptance of precisely that lifted
certificate between precisely those vertex outputs. It does not assume a
path-lifting result, a new edge relation, or an existential replacement
certificate.

These local derivation families remain explicit hypotheses of both frozen
targets. A generic path theorem does not discharge them for the original
source checker.

## Connection with the original source construction

`ApplicationCertificateLiftPath.vertex` uses the original decoded application
and its original zero default. `liftEntries` maps each original pair-coded
entry to its recanonicalized next vertex and the explicit `liftEdge` of its
original edge certificate. `liftPath` applies the original path decoder and
encoder. The accepted `InternalApplicationPathMap` calibration connects the
concrete Program map to this exact construction for every natural input at a
fixed ambient Gamma. Its internal entry and cons equations retain the actual
pair, list-cons, vertex, and lifted-edge graph witnesses.

`InternalPathChecker` supplies the corresponding concrete checker AST and its
internal nil/cons equations. A nonempty accepted path decomposes into the
original head edge and a reflexive accepted suffix; a positive path retains
the same suffix convention. The frozen generic lifting targets transfer this
structure through the literal application map using the two local rules.

The existing standard-model proof is
`ApplicationCertificateLiftPathCoreProof.actualPathLift`, which inducts over
the original entry list. Its cons case uses
`ApplicationCertificateLiftEdgeProof.actualTypedEdgePresentation` and
`actualOriginalEdgeLift`; its nil case uses the original representative
application congruence. `actualPositiveLift` preserves the original positive
checker. `ApplicationCertificateLiftPathProof.actualOriginalPositiveLift`
then handles the decoded context and object fibers, typed canonical terms,
the result-builder calibration, and the outer `pathValue` wrapper. These
theorems identify the source construction and required concrete mathematics;
their standard-model conclusions are not reflected into internal derivations.

## Remaining concrete obligations

Instantiation still requires an explicit arithmetic invariant for the
original source domain and internal derivations of its single-edge
preservation and the exact single-edge compatibility rule. In particular,
the original numeric step checker must preserve acceptance under the literal
application-step certificate transformer. The source and target
representative graphs must also satisfy the required canonical application
congruences at their actual outputs. The source's subtype-closure, typedness,
universe, and fixed-argument conditions must be supplied through the concrete
arithmetic invariant and derived graph rules.

`InternalQuotientEdgeChecker` exposes the exact original step and the two
representative checks, including their different original decoders, on all
natural inputs. That decomposition isolates these remaining local proofs;
its all-input calibration does not establish step preservation or
representative congruence.

The generic lifting targets do not assemble the context-uniform source
presentation, discharge the outer argument-object decoder and `pathValue`
fallback, or prove the concrete `CertifiedApplicationLift` premise of the
computability-downward consumer. Completion of paper06 `lem:id1` is not claimed
by this supporting path theorem.
