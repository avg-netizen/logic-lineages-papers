# Application-only original validity stack: frozen one-step prerequisites

This is a supporting component toward paper06 `lem:id1`, not a numbered
statement promotion or a proof of application-validity closure. The original
source is `../06-godel-t-termination-ordering/paper.tex`: lines 537–549 require
well-typed auxiliary syntax, finite type windows, and function-side application
reduction; lines 551–556 specify type-preserving equivalence and the quotient.

## Why a concrete recursive Program is needed

The checked original step guard exposes sourceValid(source) and
targetValid(target). The checked structural endpoint wrapper additionally
exposes argument source validity, the three original outer type tags, and
membership of the application result type. None supplies source validity of
the newly constructed source application or target validity of the newly
constructed target application. An opaque unary leaf calibrated only by
natural evaluation cannot turn those facts into an internal graph derivation.
Moving wrappers around does not discharge that missing constructor rule.

The new Definitions expose an actual Program AST which recursively opens only
application nodes. Non-application nodes retain the whole original unary
validity leaf. This does not replace lambda, constructor, variable, numbered
or ordinary-head validation by a new semantic predicate.

## Exact original codes and domain

The original application on raw term payloads is

    pair e (pair 2 (pair d (pair fp ap))).

Its typed function child is `pair (1 + pair d e) fp`; its typed argument child
is `pair d ap`. These are precisely the original type and term codecs used by
InternalApplicationCertificateConstructors.packedApplication. The already
checked original decodeType is total on every natural code, so no type code
is omitted. Arbitrary malformed term payloads, wrong constructor tags and
failed typed decodes remain in every appropriate calibration quantifier.

The target test is exactly the original decodePackedNumber.isSome. It has NO
universe filter. The source test is exactly the original rawCarrierTest, which
includes decodeUniverse and the original universeTest. At an application,
that source test requires result-type membership and source validity of BOTH
children. There is no subtype-closure assumption on S. All work is at fixed
n, arity, symbols, S and Gamma; no joint-context or uniform-Gamma package is
claimed.

## Concrete transition and bounded validator

A state is status paired with the ORIGINAL numbersNumber list of pending
packed values. Status one is live or successfully finished. Every other
status rejects. Zero is the failed state with empty worklist. Empty live
states are fixed points. A nonempty live state processes its first value:

1. If its original term-constructor tag is two, test the supplied node guard
   at its original result-type code, accepting exactly one. On acceptance,
   replace the value with its reconstructed typed function and typed argument,
   in that order. On rejection, return the failed state.
2. Otherwise test the supplied leaf at the WHOLE packed value, accepting
   exactly one. On acceptance, remove the head; on rejection, fail.

The AST uses the checked original pair/unpair/list constructor, equality,
conditional and exact-one operations. No primitive-recursive representability
witness is selected for this transition.

The Definitions also expose the complete intended bounded validator. A
literal Program.recursion repeats the transition payload(value)+1 times from
the live singleton worklist. The final checker requires BOTH status one and
an empty worklist. Thus fuel exhaustion cannot be confused with acceptance.
The target validator uses a constant-one application guard and the existing
targetValid leaf. The universe validator uses the original membership leaf
at application nodes and the existing sourceValid leaf elsewhere. The new
sourceValid is the explicit exact-one conjunction of target validator and
universe validator. Its implication to the SAME target validator is therefore
syntactic and can be proved internally without any semantic calibration.

The bounded validators are exposed definitions, not yet accepted calibrated
replacements for the old validity leaves. Their all-input calibration and
internal recursive constructor laws remain pending after this packet.

## The crucial fuel invariant

Use the sum of payload(value)+1 over all pending packed values. Do NOT use
the packed natural numbers themselves: reconstructing the function's arrow
type can increase that number. For every d,e,fp,ap, the original app payload
pair 2 (pair d (pair fp ap)) is at least fp+ap+2. This follows from the checked
Nat.add_le_pair and projection bounds, with no semantic validity assumption.
Replacing the app by its two children therefore lowers work weight by at
least one. A successful non-app leaf removes positive weight. A failure clears
the entire nonempty worklist. Hence every processed live nonempty state
strictly lowers weight, and the singleton initial weight is payload(value)+1.

This explains an implementable global bound, rather than assuming recursive
termination or using an unjustified packed-code bound. The packet freezes the
one-step strict decrease theorem. Iteration exhaustion, all-input bounded
validator calibration and an INTERNAL weight/iteration argument are future
proof obligations, not hypotheses inserted into a claimed closure theorem.

## Seven exact targets

1. ActualOriginalApplicationDecoderEquations: all-input original target/source
   decoder identities at a literal application. They reconstruct both typed
   children, preserve the source membership test and omit target membership.
2. ActualOriginalStackTransitionCalibration: equality of the concrete AST's
   evaluation with its direct numeric transition, at every raw state and for
   arbitrary Program leaves, including leaves returning numbers other than
   zero and one.
3. ActualOriginalEncodedStackTransition: exact numeric/structured transition
   compatibility under the original state/list encoding, for every status,
   worklist and pair of numeric leaf functions. The existing natural-list
   codec bijection covers every raw stack code.
4. ActualOriginalStackValidityInvariant: processing a state preserves, in
   BOTH directions, live status and validity of all pending values. The two
   instances name the original target test and source test literally. No
   original validity or successful-decoding hypothesis is added.
5. ActualOriginalStackWorkDecrease: strict payload-work decrease for every
   live nonempty state and arbitrary numeric leaves, including rejection.
6. ActualOriginalApplicationStackPush: an actual internal full-output graph
   equivalence for the concrete application frame and expanded frame, under
   the actual node-guard output-one graph at the same symbolic result type.
   Domain, result type, both payloads, suffix, state and output remain arbitrary
   object-language terms. The leaf is arbitrary and not inspected. This is a
   transition equation, NOT the entire validator's application equation.
7. ActualOriginalRecursiveSourceTarget: actual internal projection from the
   concrete recursive source conjunction to the same target validator. It
   uses no leaf calibration or external-truth-to-derivability principle.

The definition/target split is deliberate. Invariants are external statements
to prove, not certificate fields, class assumptions or new internal rules.
The internal targets contain only original Program graph premises and actual
InternalCalculus.Derivation conclusions.

## Exact remaining work and boundary

After accepting these targets, derive numeric iteration exhaustion and prove
all-input calibration of validator(constantOne, old.targetValid),
validator(member, old.sourceValid), and recursiveData against the SAME
original validity functions. Calibration must cover every natural input,
not just decoded or canonical values. The source conjunction is redundant
externally only after original source-implies-target has been proved.

Then prove internal iteration sequencing, sufficient-fuel stability and
constructor acceptance for the concrete bounded AST. Use a genuine internal
payload work measure or another explicit bounded computation argument. An
external evaluation equality is not an internal graph equation. Recover the
original caller's function and argument using the supplied original outer-tag
graphs; rawApplication itself discards those tags. The target application law
must not add source-universe validity of the target function. The source law
must retain source validity of function and argument plus result membership.

Finally use this SAME calibrated recursiveData in the original step, typed,
representative and endpoint wrappers. Do not identify different Program
graphs merely because their natural evaluations agree. Representative
congruence, the complete typed-edge bridge, positive-path invariant assembly,
joint-Gamma and outer pathValue malformed-object handling, and
CertifiedApplicationLift are not proved here. Multiset, constructor, lambda,
fundamental and closed all-term ID1 results remain pending.

## Freeze and verification

Definitions, Targets, Preflight and this correspondence are frozen before
proof authorship. Native preflight has NOT run and no compiler slot was
acquired. This preparation worker did not author proofs, edit existing frozen
sources, run Git, change resources or update the global register. Independent
specification review, bounded serialized native preflight, proof compilation,
exact target comparison and actual standard-axiom closure audits are required
before accepting the component. No full-root or remote-CI result is claimed.
