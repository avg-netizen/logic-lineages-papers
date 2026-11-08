# Structural original application endpoint: frozen supporting specification

This packet is a supporting prerequisite for paper06 lem:id1, not a promotion
of a numbered claim. The original paper is
../06-godel-t-termination-ordering/paper.tex: lines 537–549 specify the well-typed
function-side auxiliary application reduction, and lines 551–556 specify the
type-preserving primary quotient and arithmetic edge relation.

## Original meaning and concrete construction

InternalApplicationStepPeel.endpointValue is unchanged. Its input coordinates
are [domain, codomain, raw source, raw target, raw argument]. It decodes domain
and codomain with the original decodeType, source and argument with the original
decodeUniverse, and target with the original decodePackedNumber. The source and
target must have the decoded arrow type, the argument must have the decoded
domain type, and the decoded codomain must literally belong to S. Any failure
returns zero. The window S is arbitrary, with no subtype-closure assumption.

InternalStructuralEndpointGuard.endpoint is a concrete Program 5. It composes
the literal InternalOriginalStepGuard.Data.sourceValid leaf at coordinates 2
and 4, and its targetValid leaf at coordinate 3. It then conjoins the existing
InternalApplicationStepPeel.endpointTypeGuard and a unary membership leaf at
coordinate 1. The existing endpointTypeGuard is the three explicit numeric
equalities: raw source tag equals original consCode(domain,codomain), raw target
tag equals the same consCode result, and raw argument tag equals domain.
consCode is exactly the successor of the original Nat.pair Program, the original
arrow type code. No alternative pairing, decoder or code system is introduced.
Every conjunction accepts exactly output one and rejects to zero.

The one new atomic leaf computes membershipValue S e, which retains the original
decodeType e and checks literal decoded membership in S. The existential selects
one unary Program for fixed S before all natural inputs. It has no correctness
or derivability fields. The existing source/target leaves are shared rather than
reselected by this packet. There is no opaque existential endpoint Program.

## Exact three-target boundary

1. ActualOriginalMembershipProgramExists selects the unary membership Program
   with all-input calibration for every arbitrary fixed S.
2. ActualOriginalStructuralEndpointCalibration states that the concrete endpoint
   AST has the unchanged EndpointCalibrated property whenever the shared
   original validity leaves and membership leaf have their separate all-input
   calibration. It includes all natural five-tuples, failed packed/universe
   decodes, mismatched types and rejected windows, with no valid-input premise.
3. ActualOriginalEndpointAcceptanceAtArrow is an internal derivation: assuming
   the actual graph2 InternalListCodec.consCode arrow d e, acceptance of the
   concrete endpoint is equivalent to the actual source-valid, target-valid,
   argument-valid, three raw-tag and codomain-membership graphs. The forward
   direction derives the raw-tag graphs without independently supplied tag
   witnesses. The reverse direction is the exact endpoint introduction law.

The third target quantifies arbitrary body, free-variable type, symbolic terms
and Program leaves. No external calibration premise or decoded semantic object
appears in it. The cons graph is deliberately an actual original arithmetic
Program graph, not a semantic equation about type codes. Empty-context
derivations can be reused in ambient contexts by the existing weakening rule.
The target is a factorization of an explicit AST, not an assumed lifted-step,
endpoint correctness or completed typed-edge bridge rule.

## External codec fact versus internal evidence

The already checked NumberedTypeCodecTotalProof.typeDecoderTotal and
typeCodeBijection ensure every natural domain/codomain code decodes uniquely to
the corresponding original type. Thus there are no failed numeric type codes
to silently exclude, and separate type-validity leaves are unnecessary.
For packed/universe decodes, the original packedNumericSound theorem identifies
the raw outer numeric field with typeNumber of the decoded packed type. Together
these facts justify the external all-input calibration while preserving all
failed packed-term and universe cases. The proof must establish that numeric
arrow/tag equalities are exactly the original decoded-type equalities, not
assume typed inputs.

The original primitive-recursive type decoder, literal finite membership test
and allPrimitiveFunctions may select only the atomic membership Program.
Internal equality acceptance, conjunction acceptance, graph composition,
totality and functionality/output transport can support the internal target.
Neither primitive recursiveness nor semantic evaluation truth supplies an
internal validity, type, membership or acceptance graph.

## Remaining assembly and exclusions

This endpoint can instantiate the already frozen InternalApplicationStepPeel
Program 5 parameter. Its validity graphs can be obtained from compatible
original step and typed-source/argument wrappers only by proving actual
internal graph rules. Representative raw-tag transport, the compatible typed
carrier wrapper, internal membership evidence for the selected result type,
application-validity transport and a complete original typed-edge bridge still
require their own construction. Equal natural evaluation does not identify
internal graphs of different checker ASTs.

Selections are fixed-Gamma, with the membership leaf fixed only by S. This does
not provide a joint-context or context-uniform source package, settle malformed
outer pathValue behavior, or establish CertifiedApplicationLift. The remaining
multiset, constructor, lambda, fundamental and closed all-term ID1 obligations
are not discharged. No original frozen file, register or checker is changed.

## Freeze status

Definitions, Targets, Preflight and this correspondence are frozen before proof
authorship. Independent specification review and successful native preflight
are required before proof authorship. No compiler was run for this packet, no
compiler slot was acquired, and no Git action was taken. The serialized resource
profile and permitted standard axioms remain unchanged. No full-root or remote
CI result is claimed.
