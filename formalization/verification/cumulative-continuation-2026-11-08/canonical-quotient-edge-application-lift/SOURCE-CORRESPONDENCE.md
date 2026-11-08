# Canonical application and same-checker quotient-edge lifting: frozen targets

This packet freezes seven supporting targets toward paper 06 `lem:id1`.
Only definitions, exact target propositions, preflight aliases, source
correspondence and pins are supplied. Independent review must precede native
preflight and proof authorship. No proof implementation, compiler invocation,
accepted-source change, Git action or source-register promotion is included.

## Original source and unchanged selected checker

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-556, fixes the
finite subtype-closed window, original typed numbered steps, function-side
auxiliary application, primary equivalence and least-code representatives.
Lines 563-588 use typed arithmetic edges and their application descendants in
the accessibility argument. This packet addresses the local application edge
rule only. It is not the complete path, computability or accessibility proof.

The existing `InternalCanonicalDescentSelection.Data` is reused without new
fields. In particular there is no old typed program, correctness field,
endpoint law, success law, fixed-argument law or representative-congruence
field. Set R to `data.oldEdge.targetRepresentative`, V to the source-validity
program in `InternalCanonicalDescentSelection.validity data`, and member to
`data.member`. G, D, C, N and H are exactly the checked canonical fold programs:

- G checks the original root, both original children and original codomain.
- D is the bounded descent with the original R fallback.
- C(d,e,f,a) is D of the original raw application, without codomain repacking.
- N uses the original finite fold and `2 * originalPayload + 1` fuel.
- H checks the original successful singleton result state.

The Edge and typed aliases in this packet are definitionally the preceding
`InternalCanonicalQuotientEdgeSelection` definitions. Edge uses the same W,
where W is precisely the base original guarded application step conjoined
with V(raw target). Its source representative is N when V accepts and zero
otherwise; its target representative is N on every input. Typed acceptance
is exactly member(requested type), V(value), the original raw left type tag,
and T(value)=value. No H, old typed, N-fixed or extra endpoint guard is added.

The preceding canonical Edge selection is a separate prerequisite. Its
definitions and targets are frozen, and its proof work was underway when this
packet was created. This packet does not claim that pending implementation is
already checked and does not pin mutable proof files from that work.

## Exact application program and external target map

The new finite `actualJ : Program 4` has input order
`[domain, codomain, canonical function, RAW argument]`. Its literal AST is

`composition C [projection0, projection1, projection2, composition N projection3]`.

Thus actualJ(d,e,x,a) = C(d,e,x,N(a)). The canonical function x is passed to C
unchanged. There is no second N(x), no N(a)=a premise, and no replacement of
the raw argument in the certificate transformer. Even typed acceptance only
provides T-fixedness; this packet never silently changes that to N-fixedness.

Write R_old(z) for the original total
`InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma z`.
The exact `ApplicationCalibrated` target is, on every natural four-vector,

`evaluate actualJ [d,e,x,a] = R_old(ApplicationCertificateLift.applicationValue [d,e,x,R_old(a)])`.

This is an all-input equation, including zero, malformed and nonuniverse
inputs. It follows by composing the already checked all-input equations for
the actual N and C. It does not replace the original total target map with a
source-filtered default. In particular it does not assert all-input equality
to the partial `NumberedNumericApplication.canonicalApplication` function.
The latter has additional decoding, type and canonicality checks. The exact
typed application role here is the internal typed-output theorem and local
Edge theorem, not a new off-domain identification with that partial function.

## Seven frozen targets and exact premise boundaries

0. **ActualOriginalCanonicalApplicationCalibration.** Under original leaf
   calibration and subtype closure, the actualJ program satisfies the exact
   total target-map equation above on all natural inputs.
1. **ActualOriginalCanonicalRepresentativeApplicationTransport.** For
   arbitrary Data, body, variable type, context and symbolic terms, assume
   only the actual arrow constructor; V(f), left(f)=arrow; V(a), left(a)=d;
   member(e)=1; N(f)=x; original rawApp(d,e,f,a)=parent; and actualJ(d,e,x,a)=out.
   Derive V(parent) and the actual certified N(parent)=out result, together
   with V(out), left(out)=e and T(out)=out. Parent validity, G, H, successful
   child/parent runs, N(a)=a and representative congruence are not premises.
2. **ActualOriginalCanonicalApplicationTypedOutput.** From exactly
   typed(x,sigma->tau), typed(a,sigma), and actualJ(d,e,x,a)=out, derive
   typed(out,tau), where d and e are the original closed type numerals.
3. **ActualOriginalCanonicalEncodedQuotientEdgeApplicationLift.** Add only
   the actual original constructor witnesses to `corePremises`: the raw
   certificate's source, target and step; both raw applications using a;
   the original lifted step; and the original encoded lifted edge. Derive
   the very same Edge(out,other,lifted), with no new endpoint/parent facts.
4. **ActualOriginalCanonicalQuotientEdgeApplicationLift.** The witness-free
   implication has exactly these premises:
   - typed(x,sigma->tau);
   - typed(a,sigma);
   - Edge(x,y,certificate);
   - actualJ(d,e,x,a)=out;
   - actualJ(d,e,y,a)=other;
   - original edgeLift(d,e,a,certificate)=lifted.
   Its conclusion is the SAME Edge(out,other,lifted). The certificate
   transformer receives RAW a, while actualJ normalizes a internally.
5. **ActualOriginalCanonicalQuotientEdgeApplicationTypedOutputs.** The exact
   same witness-free premises imply typed(out,tau) AND typed(other,tau).
   Target typedness is not a premise; the preceding canonical Edge typed
   propagation supplies typed(y,sigma->tau).
6. **ActualOriginalSelectedCanonicalQuotientEdgeApplicationLift.** For each
   original signature, symbols, S, Gamma and table with subtype closure,
   select ONE existing Data before every body, type, variable type, context
   and term. Retain original leaf calibration, the complete preceding
   selected W/Edge/typed calibration and its internal laws, and add actualJ
   calibration plus its three internal application/edge/output-typing rules.

Targets 2-5 assume only membership calibration and subtype closure outside
the derivation. These are used for CLOSED type-code computations. No complete
leaf, representative, V, step, Edge or typed calibration is required by them.
The symbolic helper target 1 has no external calibration or subtype-closure
hypothesis at all. All internal targets retain arbitrary derivation contexts.
`InternalLaws` is a conclusion of the shared selection, never a Data field or
assumed supplier. Preflight aliases name the seven propositions in this order.

## Internal proof route, without the old presentation

This is a supplier plan, not a proof implementation.

Use the existing actual Program totality/continuation machinery to expose the
original certificate selectors and eliminate them capture-avoidably later.
`InternalQuotientEdgeCheckerSupportProof.checkerRecover` supplies W(s,t,k),
the source representative graph with output x, and N(t)=y. Recover W's V(s),
V(t) and original raw type guard from its two actual conjuncts. V(s)=1 selects
the N branch of the source representative, yielding the actual N(s)=x graph.

Query the original left selector at s internally. Apply
`InternalCanonicalResultFoldInvariantConsumerProof.actualOriginalCanonicalFoldOutputConsumer`
to V(s), that raw tag graph and N(s)=x. Its output tag agrees with the tag
recovered from the SAME canonical typed(x,arrow) AST. Program functionality
therefore transports the raw source tag to arrow. Then
`InternalOriginalStepGuardSupportProof.taggedRecover` propagates that raw tag
to t. This is internal graph reasoning, not semantic reflection or an
assumed tag-backward law for arbitrary representatives.

Recover argument V(a), its domain tag and source arrow membership from the
canonical typed graphs. Obtain codomain membership using only a CLOSED
numeral membership calculation and subtype closure. The existing
`InternalTypedEdgePresentationSupportProof.codomainMembership` and
`arrowNumeral` may be reused as these narrow closed-arithmetic suppliers,
or factored into local helpers such as closedCodomainMembership. Neither
supplier requires the old typed Data or its presentation theorem. The full
`InternalTypedEdgePresentationSupportProof.presentation`, typedComponents,
old presentation Data and old representative-tag transport are forbidden
shortcuts for this packet.

Construct the exact original endpoint directly with
`InternalStructuralEndpointGuardSupportProof.endpointAccept` from these raw
source/target tags, V(s), packed target validity, V(a), codomain membership
and the actual arrow constructor. Use the preceding canonical Edge
`ActualOriginalCanonicalEdgeApplicationStep` at the actual raw applications
and lifted step. This proves W at those parents, including V(target parent).

For each raw parent, the representative helper proves the new source and
target representative graphs. Query actual N(a)=b internally and use the
checked fold output consumer to produce the argument's successful certified
run and V(b), left(b)=d, T(b)=b. Likewise N(s)=x and N(t)=y, their recovered
raw tags and validities provide successful function-child certificates.
Functionality identifies the queried N(a) output with the argument value
inside each actualJ graph, yielding C(d,e,x,b)=out and C(d,e,y,b)=other.

Derive V(raw parent) by
`InternalCanonicalResultFoldInvariantApplicationSupportProof.rawValidity`.
Recover the original payloads and reconstruct the original application
children from their raw type tags. Build the literal G graph from this
parent validity, BOTH child validities and codomain membership. G is not
inferred from arbitrary V alone. Apply
`InternalApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure`
to the actual child certificates and exact C graph. This proves
N(rawApp(s,a))=C(N(s),N(a)) and its successful H graph. Parent source validity
then selects the N source representative; the target representative is
already N. No congruence assumption for arbitrary R or D is used or needed.

Assemble the very same Edge at the original encoded lifted certificate with
`checkerAccept`. The existing edgeLift constructor graph equations and
internal totality eliminate all raw witnesses for target 4. Target 2 uses
the same normalized-argument invariant, raw validity/tag, and D-output typed
rules directly at x, without normalizing x. Target 5 combines target 2 with
the preceding canonical Edge typed propagation to type the second output.

## Old-target correspondence and deliberate replacement

The earlier `InternalCertifiedQuotientEdgeApplicationLift` packet is a proof
organization example, not a drop-in supplier for this checker:

- Its `ActualOriginalCertifiedApplicationStepClosure` is replaced by the
  separately frozen canonical Edge application-step target. The new W has
  no H guards and must not inherit the old argument H premise.
- Its `ActualOriginalCertifiedEncodedQuotientEdgeApplicationLift` corresponds
  to new target 3, but the old Data/typed/core/combine ASTs are not substituted.
- Its `ActualOriginalCertifiedQuotientEdgeApplicationLift` corresponds to new
  target 4. The old fixed-argument/old-combine representative transport is
  replaced by actualJ and the new symbolic certified-fold helper.
- Its `ActualOriginalSelectedCertifiedQuotientEdgeApplicationLift` corresponds
  to new target 6, with the smaller existing canonical Data and SAME preceding
  W/Edge/typed selection, plus exact actualJ calibration and output typing.
- New targets 0, 1, 2 and 5 explicitly state the target-map, representative
  transport and typing obligations that cannot be silently imported from
  the older ASTs. No earlier accepted target or proof is edited.

## Freeze, provenance and limits

`FROZEN-SOURCE-PINS.json` hashes these three specification modules and this
correspondence. `SOURCE-PINS.json` records their full local import closure
and stable prospective suppliers, including meta imports, together with the
paper, checker/toolchain inputs and prior accepted/frozen evidence.
`FROZEN-SPECIFICATION.json` records exact AST/premise boundaries, target names,
source hashes and static checks. No mutable new canonical Edge proof file is
included. A future acceptance must separately audit its completed supplier.

Static delimiter, import, source-preservation and hash checks are not Lean
elaboration or proof acceptance. Any native preflight/proof work requires
the coordinator's release and sole compiler slot. Only `scripts/check.py`
may run Lean, at the unchanged 2048 MiB heap, 1536 MiB process-tree RSS,
2048 MiB minimum free memory, one thread, 90 CPU seconds, 180 wall seconds
and existing upstream-cache-only profile. Allowed axioms are the usual
propext, Classical.choice and Quot.sound foundations. The current deadline
is 2026-11-08 18:00 UTC; this freeze does not authorize work beyond it.

No path or context-uniform lift, outer pathValue wrapper, discharge of
CertifiedApplicationLift, complete computability closure, multiset/constructor/
lambda/substitution proof, all-term accessibility, paper06 lem:id1 completion,
source promotion, full-root build, remote CI or publication is asserted.
