# Original internal application-validity constructor closure

This four-target supporting packet supplies the next internal validity
obligation toward paper 06, `lem:id1`. It refers to the already frozen
bounded-stack validator and concrete `recursiveData` without changing either.
The desired result is an actual proof in `InternalCalculus.Derivation body []`,
not calibration in the natural-number model or a new closure premise. The
packet is a specification freeze, not a completed derivation or promotion of
any numbered source statement.

## Exact syntax and minimal imports

The new Definitions file imports only
`InternalApplicationValidityStackAppendDefinitions`. Targets imports only
the new Definitions, and the comparator-only Preflight imports only Targets.
There are no new proof files or semantic-calibration imports in this packet.
Existing transitive suppliers are left unchanged. In particular the actual
`validator`, `fuel`, `initial`, `run`, `finished`, `transition`, `iterate`,
`recursiveData`, list codec, pairing and application constructors retain
their original definitions.

`applicationConstructors arrow d e fp ap fn arg parent` is exactly:

    consCodeGraph arrow d e AND
    pairingGraph fn arrow fp AND
    pairingGraph arg d ap AND
    packedApplicationGraph parent d e fp ap.

The original arrow is `1 + pair d e`. The function and argument are therefore
the literal packed values `pair arrow fp` and `pair d ap`. The parent is
`pair e (pair 2 (pair d (pair fp ap)))`. These descriptions explain the
unchanged programs; the formula itself uses their original internal graph
relations and shares the same symbolic terms at every occurrence. It does
not use external equalities, typed semantic values or decoding witnesses.

`endpointApplicationPremises old member arrow d e s t a sourceApp targetApp`
contains only the original arrow cons graph, acceptance of
`InternalStructuralEndpointGuard.endpoint (recursiveData old member) member`
at `[d,e,s,t,a]`, and the two original `application` graphs at `[d,e,s,a]`
and `[d,e,t,a]`. The raw constructor is deliberately `application`, not
`packedApplication`: it discards only the outer type fields of the two
original child values. No raw tag, payload equality, reconstructed value or
codomain membership is silently assumed outside the actual endpoint.

## Four exact targets

Every target quantifies an arbitrary positive body, arbitrary variable type,
and arbitrary original object-language arithmetic terms. Validator targets
quantify arbitrary actual unary node and leaf programs. The recursive
endpoint target quantifies arbitrary old `Data` and a unary member program.
There are no calibration assumptions on any of them.

1. **ActualOriginalFinishedAcceptance.** The actual unary finished program
   accepts a state at one if and only if that state equals the literal
   success-state term `succTerm (succTerm zeroTerm)`. The state is two because
   the unchanged status-one/empty-work encoding is `pair 1 0 = 2`. This is an
   internal equivalence on arbitrary raw states, not an evaluation lemma.
2. **ActualOriginalValidatorSingletonSuccess.** Given the actual unpair-right
   graph for the value's payload and the actual cons graph of the singleton
   `[value]`, frozen validator acceptance at one is equivalent to
   `successfulWork node leaf (succTerm payload) singleton`. The two premise
   graphs constrain all witnesses. The count cannot be replaced by a free,
   larger or externally chosen bound.
3. **ActualOriginalValidatorApplicationClosure.** The four original
   constructor graphs above, node acceptance at the same codomain `e`, and
   acceptance of both exact typed children by the same validator imply
   acceptance of the exact parent by that unchanged validator. This result
   holds for arbitrary node and leaf ASTs. The leaf is not consulted at the
   application-opening step. The final validator uses its own original
   parent-payload-plus-one fuel, without a supplied success or closure oracle.
4. **ActualOriginalRecursiveEndpointApplicationValidity.** The endpoint
   premises above imply both source validity of `sourceApp` and target
   validity of `targetApp` for `recursiveData old member`. Source is exactly
   the conjunction of target validation and universe validation. Target is
   the validator with constant-one node guard and old target leaf, with no
   source-universe filter on `t` or `targetApp`.

## Internal route and exact parent fuel

The following is a permitted proof plan, not additional hypotheses of any
target. Each bridge and arithmetic witness must be proved in the unchanged
internal calculus.

Recover each child validator's singleton `successfulWork` through target 2.
The pair graphs force the function and argument payloads to be exactly `fp`
and `ap`. Original append nil/cons equations construct the graph joining the
two singleton lists. The frozen
`InternalApplicationValidityStackAppendTargets.ActualOriginalSuccessfulWorkAppend`
then yields success of `[fn,arg]` after

    childFuelSum fp ap = addTerm (succTerm fp) (succTerm ap).

Use the actual `applicationFrame` and `expandedFrame` programs with empty
suffix. The checked `ActualOriginalApplicationStackPush` and original
numeric front-successor law add exactly one parent-opening step. This gives
singleton-parent success after `succTerm (childFuelSum fp ap)`. No equality
with an untouched suffix after a padded child count is claimed: the append
supplier is the truthful summed-count success statement.

Decompose the same original packed parent constructor into shared internal
pair witnesses `payload`, `middle`, and `children`:

    pairGraph payload two middle AND
    pairGraph middle d children AND
    pairGraph children fp ap,

with parent `pair e payload`. These are precisely
`InternalPairingSumBounds.applicationPayloadWitnesses`, not a bound on the
reconstructed typed child numbers. The checked
`ActualOriginalApplicationParentFuelBound` proves

    succTerm (childFuelSum fp ap) <= succTerm payload.

The existing internal `InternalUnpairReverseSyntaxProof.weakOrderCases`
provides a symbolic padding witness `w` with

    addTerm (succTerm (childFuelSum fp ap)) w = succTerm payload.

The original transition at the success state two is internally fixed. The
checked numeric iteration addition-fusion and fixed-point laws therefore
pad the successful execution to exactly `succTerm payload`. The proved
singleton bridge reassembles acceptance of the unchanged parent validator.
In particular, no standard-model termination, semantic truth-to-derivability
principle, chosen counting program, alternate iteration AST, altered fuel,
or assumed application-closure field is used.

## Concrete recursive endpoint instantiation

The checked original structural endpoint factorization at the supplied
arrow cons graph derives all three validity graphs, all three raw outer
tag graphs and membership at the same codomain `e`:

    sourceValid s = 1; targetValid t = 1; sourceValid a = 1;
    left s = arrow; left t = arrow; left a = d; member e = 1.

These are internal program graphs. They are not semantic equalities or
extra target assumptions. Decompose each source acceptance using the
actual conjunction in `recursiveData`: obtain both target and universe
validator acceptance for `s` and `a`. In particular the argument's target
acceptance is derived from source acceptance, also supplied by the checked
`ActualOriginalRecursiveSourceTarget`.

Use totality of the actual right-selector graph to bind raw payloads of
`s`, `t`, and `a` inside the derivation. Combine the endpoint's left-selector
graphs with those right-selector graphs through the checked original
unpair reverse inverse. This reconstructs the exact original pair graphs,
without new child tag or codomain assumptions. The original `application`
graph equation reduces each raw application to `packedApplication` at those
same payloads. Thus target 3 applies to the universe validator on `s,a`
with node guard `member`, and to the target validator on both `s,a` and
`t,a` with the constant-one node guard. Introduce the actual source
conjunction for `sourceApp`; retain only target validity for `targetApp`.

This route never assumes that `t` belongs to the source universe. It does
not require the window to be subtype-closed, inspect old leaf correctness,
or turn the separately checked all-input recursiveData calibration into an
internal inference rule. That external calibration remains a separate
supplier for semantic use after the internal result is proved.

## Paper correspondence and exclusions

Paper 06 lines 537-549 fix the source universe and include ordinary auxiliary
application and its function-side reduction rule; lines 551-556 specify the
arithmetic quotient relation, and lines 558-560 state `lem:id1`. The present
packet is an internal syntactic validity supplier for the original local
application rule. The generic arbitrary-program theorem is an intermediate
calculus fact and does not replace the source theorem's original semantics.

Representative congruence, full original typed-edge and path assembly, the
outer malformed-object path wrapper, joint-context uniformity,
`CertifiedApplicationLift`, source multiset/constructor/lambda arguments,
and the closed all-term accessibility endpoint remain separate obligations.
No numbered statement, full-root build, remote CI or publication is claimed.

## Freeze and validation boundary

The manifests pin these new Definitions, Targets, comparator-only Preflight,
this correspondence, selected unchanged source/calculus APIs and the paper.
They are exact-source specifications, not a compiled dependency receipt.
The successful-work append Definitions/Targets are stable after their
documented binder-only amendment and have independent review and native
preflight PASS. Its proof author is working separately; this packet neither
imports those live proof files nor claims append proof acceptance.

Independent review and bounded serialized native preflight for this packet
must pass before proof authoring. Neither has been performed by this worker.
No compiler slot is held and no compiler has been invoked. Later checks must
use `scripts/check.py` under a fresh sole-slot grant and the unchanged
2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum-free, one-thread, 90-second CPU
and 180-second wall profile with pinned upstream cache only. Allowed axioms
remain only `propext`, `Classical.choice` and `Quot.sound`.
