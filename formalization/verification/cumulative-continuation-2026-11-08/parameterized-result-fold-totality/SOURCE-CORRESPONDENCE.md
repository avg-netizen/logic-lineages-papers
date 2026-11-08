# Parameterized original result-fold totality: frozen internal prerequisite

This packet freezes four internal derivability targets only. It contains no
new proof, evaluator, compiler run or acceptance claim. Its main obligation is
an actual internal strong-payload induction proving that the unchanged
parameterized machine succeeds on every original packed natural input, for
arbitrary total Program callbacks. No numbered source statement is promoted.

## Source boundary

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-549, fixes the
well-typed numbered reduction rules. Lines 551-556 retain the primary
quotient, least-code representatives and arithmetic H/R; lines 558-560 state
`lem:id1`, arithmetic accessibility. The present result is a generic machine
prerequisite supporting that programme. It proves neither validity nor source
accessibility. The machine's `goodRunP` success bit is not the paper's one-step
relation H.

The existing parameterized ASTs are reused literally:

- G and L are arbitrary `Program 2`, applied to `[wholeInput,p]`.
- C is arbitrary `Program 5`, applied to `[d,e,functionOutput,argumentOutput,p]`.
- `openGuardP`, `transitionP`, `iterateP`, `runP` and `foldP` are unchanged.
- `goodRunP` is the existing original `goodState` composed with `runP`.
- Fuel is the original `succ(payload+payload)`, where payload is the original
  right projection of the input. It does not depend on p or output size.
- The certified formula is the previously frozen `certifiedFoldP`: BOTH the
  actual `goodRunP=1` graph and actual `foldP=out` graph at one identical p.

Success means status one, empty work and exactly one result, which may be
zero. Default zero from the raw output selector does not establish this shape.
Arbitrary malformed packed inputs remain in scope. The callbacks are total by
the original internal Program theorem, not because totality is supplied as a
new premise or selected as a callback field.

## Four exact targets

0. **Payload-uniform certified totality.** The predicate at payload n binds
   every original packed input x and every parameter p INSIDE its original
   object-language universal block. The actual graph `right(x)=n` implies an
   object-language existential y with `certifiedFoldP(y,x,p)`. All raw type
   fields are included because x is arbitrary. No requested type, validity,
   membership or source guard appears. The only induction coordinate is n;
   the entire packed input, its raw type and p are not held fixed or bounded.
1. **Global certified output.** For arbitrary symbolic input x and parameter
   p, derive the internally quantified certified output without premises.
   Internally obtain the actual right-selector output and instantiate target 0.
2. **Actual-fold output success.** An actual `foldP(x,p)=out` graph implies
   actual `goodRunP(x,p)=1`. The proof must use target 1's internally proved
   success, not external semantic calibration or output positivity. Conjoining
   the original supplied graph then certifies that same supplied output.
3. **Application equation without supplied child success.** Under the original
   application constructor graphs, actual `G(parent,p)=1`, and the actual raw
   child fold graphs at p, the actual parent fold graph is equivalent internally
   to `C(d,e,functionOutput,argumentOutput,p)=out`. There are no child H=1
   premises. The original constructors share d, e, fp and ap, and C receives
   function output before argument output despite the original stack order.

All four targets quantify over arbitrary positive body, variable type, context
Gamma and symbolic terms. Callback ASTs precede those variable-level choices.
The same p is used in each child, parent and callback. No target is an external
Nat evaluation proposition, a recursive semantic fold equation, an implication
from totality/calibration assumptions, or a redefinition of the desired graph.

## Feasibility and required internal proof route

The generic guard does NOT need to be Boolean. `openGuardP G` is already the
original normalized `InternalAcceptance.conjunction` of the lifted original
tag-two test and G. Split internally on its exact-one graph. The generic
`InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject`, valid at
any arity, derives the actual zero graph in the rejecting case. Rejection is
not replaced by the unsupported inference that a non-one arbitrary G is zero.
Use original Program totality to obtain L(x,p)'s output and the separately
frozen parameterized certified leaf closure to finish that branch.

For acceptance, use conjunction recovery to obtain both the tag-two graph and
G(x,p)=1. Take the original selectors internally, then reconstruct the original
nested pair graphs. The accepted original
`InternalApplicationResultStackCompositionFrameCoreProof.atQueries` contains
this reconstruction pattern without validity premises. Its reusable suppliers
are `InternalApplicationCertificateConstructorsSupportProof.reconstructPair`
and `InternalApplicationStepPeelComponentsProof.packedAtPairs`. In detail,
recover x=pair(e,payload), payload=pair(2,middle), middle=pair(d,children),
children=pair(fp,ap); construct arrow=cons(d,e), fn=pair(arrow,fp) and
arg=pair(d,ap). These are precisely the existing application constructors.

The checked original `InternalPairingSumBoundsProof` gives fp+ap+2 <= payload.
The accepted `InternalCanonicalResultFoldOpeningBoundsProof.payloadStrictChildren`
extracts fp < payload and ap < payload from those literal pair graphs, without
validity or canonical premises. Instantiate the smaller-payload hypothesis at
BOTH reconstructed packed children and the SAME p. Their whole packed codes,
type fields and output values need not decrease. Obtain C's actual output by
original Program totality and use the separately frozen parameterized certified
application closure. The existing internal strong-induction rule must discharge
this step. Neither a supplied induction step nor semantic truth is allowed.

For target 3, targets 1/2 supply child certifications. The forward application
closure supplies the parent fold graph from a C graph. For the reverse
implication, take an internal C-output witness, apply that closure, and identify
it with the given parent output through original Program functionality. Thus
no separate reverse machine-calibration theorem is assumed.

The parameterized certified-closure proof packet is pending. Only its stable
definitions, targets and preflight files are pinned, never its changing proof
or acceptance files. The parameterized external fold-calibration packet supplies
only the existing `goodRunP` definition and frozen specifications; none of its
external theorems, `semanticFoldP` evaluation claims or semantic reflection may
be used to supply internal derivability. The parameterized composition packet
likewise contributes only its stable specification files in this freeze.

## Freeze and next gates

`FROZEN-SOURCE-PINS.json` pins the three new Lean specification files and this
correspondence. `SOURCE-PINS.json` pins their full local import closure, stable
accepted proof suppliers for the planned argument, the three pending packets'
stable specification files, the manuscript and unchanged build inputs.
`STATIC-CHECKS.json` records syntactic shape, exact comparator coverage, hash
verification, closure and the absence of proof bodies. Static checks do not
establish Lean elaboration or mathematical acceptance.

The next gates are independent frozen-byte review, separately authorized
sole-slot comparator preflight, acceptance of the parameterized certified
closures, separately authorized proof authorship, exact frozen-type aliases
and actual standard-axiom closure audits. No compiler slot was requested or
held for this freeze. The unchanged profile is 2048 MiB heap, 1536 MiB RSS,
2048 MiB minimum-free guard, one thread, 90 CPU seconds and 180 wall seconds,
using `scripts/check.py` and the pinned upstream cache. Hard cutoff:
2026-11-08 18:00 UTC. Allowed axioms remain only `propext`, `Classical.choice`
and `Quot.sound`.

## Explicit exclusions

No canonical representative selection or congruence, uniform canonical/path
correctness, source checker correctness, unconditional CertifiedApplicationLift,
source constructor/lambda/substitution proof, all-term accessibility or paper06
`lem:id1` completion follows merely from this freeze. Removing these machine
success premises does not discharge the remaining semantic invariants of the
uniform pipeline. No new AST, parameter-specialized unary interpreter, state
encoding, padded fuel, nonzero-output restriction, accepted-source edit,
register change, dependency/CI change, full-root build, remote CI or Git action.
