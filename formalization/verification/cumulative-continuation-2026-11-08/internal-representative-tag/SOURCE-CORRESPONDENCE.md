# Original representative outer tags: frozen supporting specification

This packet is a prerequisite for paper06 lem:id1, not a completed numbered
statement. In ../06-godel-t-termination-ordering/paper.tex, lines 537-549 state
the typed numbered rules and function-side application reduction; lines 551-556
state that primary equivalence preserves types and that the arithmetic edge
relation uses least-code representatives. These targets preserve the original
numeric definitions, including their behavior outside the source theorem's
subtype-closed windows.

## Original source and target functions

The source function is the existing
InternalQuotientEdgeChecker.sourceRepresentativeValue: it returns zero when the
original decodeUniverse fails, and otherwise the original representativeCode.
decodeUniverse retains its literal universe filter. The target function is the
existing targetRepresentativeValue: it uses decodePackedNumber, WITHOUT a
universe filter, and otherwise has the same representative and zero default.
No target-universe requirement or successful-decoding premise is added.

The new wrapper is an explicit unary Program AST. It normalizes the supplied
validity program by equality to one, returns zero on rejection, and otherwise
returns pair(left(raw input), right(old representative(raw input))). The pair
and both projections are the already calibrated original numeric ASTs. This
reconstruction is a different Program from the old representative. Equality of
natural evaluations never identifies their internal graph formulas.

withRepresentatives reuses the EXACT sourceValid and targetValid leaves from
InternalOriginalStepGuard.Data. It replaces only the two representative fields
of the existing InternalQuotientEdgeChecker.Data and preserves stepProgram
literally. Neither record nor wrapper contains proof, correctness, congruence,
typed-carrier, endpoint, lift or derivability fields.

## Exact external obligations

ActualOriginalRepresentativeOuterType concerns the original representativeCode
for every packed term and arbitrary symbols, S and Gamma. Its unpair-left field
equals the input term's original typeNumber. There is no subtype-closure or
universe-membership premise. The previously checked typedRepresentativeAttained
theorem, which has both premises, is therefore insufficient on its own.

A direct source-preserving proof is available through the original finite
candidate construction. classCodes labels every candidate with q.1;
decodePacked preserves that label on success. Thus every original vertex has
that type, and the checked reachableBound puts every primaryClass member among
those vertices. The minimum of classNumbers is attained in that finite class.
Applying the original packedNumber and Nat.unpair equations then gives the
target without appealing to correctness of primary equivalence for arbitrary S.

ActualOriginalRepresentativeWrapperCalibration retains the EXISTING complete
InternalQuotientEdgeChecker.Calibrated predicate. From calibration of the two
shared validity leaves and the old data, it proves calibration of the concrete
replacement data. Consequently both original representative functions remain
unchanged on every natural input, while stepProgram remains literally the old
AST. Successful original decoding gives the raw input's packedNumber; the
outer-type target makes the reconstructed pair equal to the old representative.
On decoder failure the original representative and wrapper both return zero.
This covers non-subtype-closed S and packed targets outside the source universe.

The external statement is fixed-Gamma and fixed-window, like the existing
quotient-edge packet. It does not select one uniform Program before symbolic
windows or contexts. No new representability witness is required: existing
calibrated original representatives and shared validity programs are wrapped.

## Exact internal obligations

Both internal targets quantify arbitrary Program leaves, positive bodies,
free-variable types and symbolic terms. Their representation premise contains
an actual validity output-one graph and the actual wrapper output graph. It
contains no semantic calibration, valid-decode assertion or reflection rule.

ActualOriginalRepresentativeTagsEqual says that independently supplied actual
unpair-left graph outputs for the raw input and representative output are equal.
ActualOriginalRepresentativeTagTransport is stronger for the intended consumer:
an actual unpair-left graph for the representative OUTPUT yields the same graph
for the RAW INPUT, without a supplied raw tag witness. The converse also holds.
The original internal composition, normalization, conditional, pairing inverse,
program totality and graph functionality rules can establish these properties.
Empty-context derivations may be weakened by the existing calculus rules.

## Remaining application-lift boundary

The raw certificate source need not equal the canonical source vertex. For a
quotient-edge checker built with withRepresentatives, its existing decomposition
exposes the wrapper graph mapping that raw source to the supplied vertex. The
same shared source-validity leaf may be exposed by the original step guard.
Once a compatible typed-carrier checker separately supplies the vertex's actual
outer-tag graph, the new transport rule can carry that tag back to the raw
certificate source. The step-guard rule can then carry it to the raw target.
This describes a future composition, not an accepted result of this packet.

There is no canonical typed-entry theorem here. There is no representative
application-congruence theorem, and replacing representative ASTs in an old
edge/path package still requires explicit selection and graph-level assembly.
Application validity, endpoint guards, joint-context uniformity, malformed
pathValue handling, CertifiedApplicationLift, constructor/multiset/lambda/
substitution/fundamental arguments and full paper06 ID1 remain beyond this
packet's claims. No numbered register entry changes.

## Freeze and admission status

Definitions, Targets, Preflight and this correspondence are frozen before proof
authorship. Independent review and successful native preflight are required
before proof authoring. This worker ran no compiler, authored no proof files,
changed no existing frozen file, and took no Git action. The serialized native
resource profile and standard-axiom acceptance policy remain unchanged. No
full-root build or remote-CI result is claimed.
