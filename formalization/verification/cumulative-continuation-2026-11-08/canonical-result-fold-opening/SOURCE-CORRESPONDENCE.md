# Canonical result-fold opening: frozen prerequisite

This packet freezes two internal supporting targets toward paper 06 `lem:id1`.
It contains specifications only. No proof file, native preflight, compiler
launch, numbered-source promotion or Git operation is included. Independent
static review must precede any native preflight or proof authorship.

## Original source and selected leaves

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-560, fixes the
finite subtype-closed type window, original auxiliary application, primary
equivalence and least-code representatives. Lines 551-556 require the actual
least representatives, not arbitrary valid terms. The checked
`InternalCanonicalDescentSelection` packet supplies an explicit R/V/D/T
selection without an old typed checker or successful-fold/fold-fixed conjunct.
This packet does not alter that selection or its calibrated Data.

For its intended later specialization, take one existing
`InternalCanonicalDescentSelection.Data data` and use exactly:

- R = `data.oldEdge.targetRepresentative`;
- V = `(InternalCanonicalDescentSelection.validity data).sourceValid`;
- member = `data.member`;
- D = `InternalCanonicalDescentSelection.fallbackRepresentative R V`;
- T = the unchanged `InternalBoundedDescentNormalizer.transition R V`.

The new internal targets are stronger in scope than this specialization: they
hold for arbitrary finite unary V and member Program leaves, every positive
body, variable type, derivation context and symbolic original parent code.
They require neither calibration nor subtype closure. R is not needed by the
opening targets because opening examines only original input values.

## Concrete new guard and fold aliases

All numerical selectors, pairing and source-list constructors are the existing
original Program ASTs. For every raw input x, including malformed ones, set:

    e  = left(x)
    p  = right(x)
    d  = left(right(p))
    fp = left(right(right(p)))
    ap = right(right(right(p)))
    arrow = cons(d,e) = 1 + pair(d,e)
    fn = pair(arrow,fp)
    arg = pair(d,ap)

`rootCodomain` is exactly the raw LEFT field of the original root. The arrow
is the original source-type cons of this codomain and the extracted domain.
The function and argument are original reconstructed typed child codes, not
normalized outputs, old representatives, raw payloads alone or external decodes.

`rootGuard V member`, abbreviated G, is the literal right-associated sequence
of existing exact-one `InternalAcceptance.conjunction` Programs:

    V(x) AND V(fn) AND V(arg) AND member(e).

Every conjunct must output exactly one. A nonzero output such as two is not
acceptance. The unchanged `InternalApplicationResultStack.openGuard G` adds
its separate original constructor-tag-equals-two test. Full opening acceptance
therefore entails the application tag as well as all four stated factors.

Only the following concrete aliases are added for the later canonical fold:

- `leaf R V` is D on the WHOLE input, including its unchanged R fallback.
- `combine R V` is D composed with the ORIGINAL `application` AST on inputs
  `[domain,codomain,functionOutput,argumentOutput]`. That AST discards only
  the outer type fields of these two outputs before constructing the original
  raw application. It is NOT the older `pair(codomain,right(R(rawApp)))`
  codomain-repacking combine and has no extra output-tag overwrite.
- `foldN R V member` is the existing result stack fold at G, this D leaf and
  this combine. `goodRunH` is the existing actual goodRun Program at precisely
  the same three leaves. Both retain the original `2*inputPayload+1` fuel.

These aliases do not prove a fold invariant or assert equality with any old
fold, representative or success checker. Existing old ASTs, off-domain defaults,
source/target distinction, checked new Data and all source files are unchanged.

There is deliberately no external calibration target in this minimal packet.
In particular G=V on all raw inputs is NOT claimed. A later external decision
calibration would have to prove the complete tag-2 opening decision agrees
with the old tag-2/V decision on all natural inputs, using original source
facts on the tag-2 branch. Nothing here supplies that as an internal rule.

## Exact graph factorization

`openingAccepted V member parent` is the original arithmetic Program graph of
`openGuard G` at one and the original parent. It is neither a semantic truth
predicate nor an atom added to the calculus.

`openingWitnesses` exposes ten shared original terms in the fixed order:

    payload, middle, children, arrow, d, e, fp, ap, fn, arg.

Its conjunction contains all of the following:

1. The unchanged `InternalApplicationValidityClosure.applicationConstructors`:
   original cons(arrow,d,e), pair(fn,arrow,fp), pair(arg,d,ap), and the actual
   `packedApplication(parent,d,e,fp,ap)` graph.
2. Actual V(parent)=1, V(fn)=1, V(arg)=1 and member(e)=1 graphs, in that order.
3. Actual original left/right selector graphs for parent=(e,payload),
   fn=(arrow,fp) and arg=(d,ap). The codomain e is therefore the actual root
   left field, not an unrelated type witness.
4. The existing `applicationPayloadWitnesses`: pair(payload,2,middle),
   pair(middle,d,children), pair(children,fp,ap).
5. BOTH original internal strict-order formulas fp<payload and ap<payload.

`opened` is the existing `InternalFiniteBlocks.block` over this exact matrix.
The parent alone remains a free input. The ten witnesses are object-language
existential variables, not natural-number witnesses supplied by a decoder.
No source inversion, correctness, payload bound, successful run, child fold
output, fixed point or induction hypothesis is assumed.

### Target 0: ActualOriginalCanonicalFoldOpeningFactorization

For arbitrary V/member, body, variable type, context and parent, derive:

    openingAccepted(V,member,parent) iff opened(V,member,parent).

The forward direction must derive every constructor, selector, validity,
membership and strict-bound fact internally. There is no external tag or
application constructor premise. The reverse direction reconstructs acceptance
from the same original shared witnesses. This is an unpremised internal iff,
not only a theorem conditional on a previously supplied decomposition.

### Target 1: ActualOriginalCanonicalFoldOpeningContinuation

From an actual derivation of openingAccepted, eliminate into any formula psi.
The continuation quantifies every new variable type beta, relabeling j,
extended context Delta and the ten shared witnesses. It receives preservation
of all relabeled original hypotheses and an actual derivation of the exact
openingWitnesses matrix, then derives relabeled psi. The conclusion is a
derivation of psi in the original context. This is the existing calculus's
relabel-safe existential-elimination pattern, not semantic witness selection.

This interface is designed for a later strong induction on the original
parent payload. The original child right-selector graphs identify the two
smaller payloads at the reconstructed original child codes. Induction must
apply to those child codes with these payload bounds. Neither packed child
codes nor normalized output codes/payloads are claimed smaller than the parent.
The subsequent fold invariant itself is outside this packet.

## Concrete checked supplier route, not additional premises

The forward proof can use existing Program totality/query elimination for the
original selectors and constructors. The checked
`InternalApplicationResultStackCompositionFrameCoreProof.atQueries` contains
the relevant reverse reconstruction pattern: hpv for the parent, hpn for the
payload/tag pair, hpb for the domain/children pair, and hpch for the two child
payloads, followed by its expandCase application-constructor reconstruction.

Use existing `reconstructPair`, `pairLeft`, `pairRight`, `packedAtPairs` and
`fieldsAtPairs` to recover the original four pair graphs, original cons arrow,
packed parent and selector equations. Exact-one conjunction elimination and
Program composition functionality identify V's two queried inputs with these
same reconstructed original children. The tag equality comes from the actual
openGuard graph, never from decoding or a new source inversion premise.

The checked
`InternalPairingSumBoundsProof.actualOriginalApplicationPayloadChildFuelBound`
applies to the recovered literal payload witness graphs and gives
(fp+1)+(ap+1)<=payload internally. Existing internal addition/order laws then
yield fp<payload and ap<payload. These strict bounds are conclusions. No
normalized-output bound is needed or permitted. All these suppliers are
ordinary existing checked declarations, not new target hypotheses.

Finally use the existing finite existential introduction/elimination and
renaming rules. The finite witness order is explicit so target 1 can consume
target 0 without ambiguity or an out-of-scope semantic choice argument.

## Freeze and verification boundary

The only new Lean files are definitions, two target propositions and two
preflight proposition aliases. No theorem implementations, proof placeholders,
axioms or unsafe/native decision shortcuts are added. Text-only static checks
and transitive import inventories are not elaboration or proof acceptance.

`FROZEN-SOURCE-PINS.json` pins the three specifications and this correspondence.
`SOURCE-PINS.json` inventories the complete transitive local import closure of
those specifications and listed prospective checked suppliers, including meta
imports, plus original paper/toolchain and accepted supplier evidence. It is a
static inventory, not a source-matched compiled-closure receipt.

Any subsequent native work requires the coordinator's independent review,
release and sole serialized compiler-slot grant. The unchanged script/profile
is `scripts/check.py`, 2048 MiB heap, 1536 MiB process-tree RSS, 2048 MiB minimum
free, one thread, 90 CPU seconds, 180 wall seconds and existing upstream cache
only. Accepted final axiom closure may contain only propext, Classical.choice
and Quot.sound.

No full canonical fold invariant, all-input G=V equation, new fold calibration,
representative application congruence, quotient-edge/path lift,
CertifiedApplicationLift, constructor/lambda/substitution closure, all-term
accessibility, `lem:id1`, numbered-source promotion, full-root build, remote CI
or publication is claimed.
