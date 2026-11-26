# V2 namespace-resolution repair

V1 frozen Targets, ComparatorGate and SOURCE-CORRESPONDENCE are preserved byte
for byte. Its native gate failed at Targets with receipt1794920255355044976-7:
`open ...CalibratedPrimary (Membership)` wrongly attempted to open a namespace
as if it were a declaration. V2 explicitly imports MembershipDefinitions and uses
the actual fully-qualified Membership.contains constant. The only other Lean
change is this packet namespace V2. The intended mathematical expression is
identical: original H/G/Q, original primary and unchanged edge B; admitted seed,
output graph and membership imply same-parameter target admission. No generic Q,
AST relocation, weakened guard or new success premise is introduced. V1 had no
compiled endpoint, so no old/new kernel equivalence is claimed. Fresh review,
freeze and named comparator gate are required before proof authoring.

## Preserved original source rationale

# Original filtered primary typed-carrier invariant

Proposed exact internal endpoint only; no proof or acceptance yet.

## Why unrestricted raw exchange typing was the wrong goal
NumberedExchangePrimrecTargets.ActualPackedCalibration quantifies BOTH endpoints
as Packed Symbol arity Gamma. NumberedExchangeCalibrationProof.termSound likewise
receives an already typed target AuxTerm. Neither says raw codeExchange preserves
typing on arbitrary raw Code endpoints. NumberedExchangeNeighborhoodDefinitions
ordinaryNeighbors and numberedNeighbors use permutations.filterMap followed by
argumentsFromList at the destination head's ORDERED argument-type list. The
original reconstruction rejects positional annotation mismatches. Raw headMove
retains the permutation but omits this reconstruction test. The verified
same-application-head swap diagnostic therefore obstructs unrestricted raw typing
preservation, not the original typed neighborhood theorem.

## Actual original numeric caller
ID1Completion/ContextUniformPrimaryDefinitions.lean defines:
1. classCodes using the original size/label/context bounds and 2*size fuel;
2. candidates = classCodes.filterMap (rawStructuralDecode arity Gamma);
3. vertices = seed :: candidates;
4. step = reached ++ pool.filter (fun r => reached.any (packedCodeExchange ... r));
5. reachable and primaryList iterate this step inside that SAME pool.
NumberedUniformPackedDecodingDefinitions.rawStructuralDecode retains the literal
raw pair iff the existing decodeTerm succeeds. Thus the raw edge is intentionally
broader than the typed relation, but original primary reachability only selects
from already filtered vertices. Its target typing comes from the pool filter,
not from a false preservation theorem for the raw edge.

## Literal internal AST
The endpoint fixes H = OriginalConcreteHeadSignature.signature n arity and
G = OriginalDecodedContextValidity.contextGuard n. It uses T = the existing
OriginalTypedDecoder.target H G, Q = OriginalCandidates.candidates n arity H,
and the existing SeededPrimaryPool.primary T Q (TypedPrimaryEdge.edge B).
The original installed structural supplier B is universally quantified and kept
unchanged. This is stronger than requiring its native calibration, since the
carrier invariant depends only on the literal pool-selection algorithm. It
applies in particular to B chosen by OriginalCandidateInstallation.SelectedTuple;
no alternate edge is installed and no relation is weakened.

## Exact premises and proof obligations
Premises are admitted seed, actual primary output graph and actual output-list
membership. Conclusion is original T(candidate, SAME parameter)=1. There is NO
premise of target typing, pool membership, successful rawStructuralDecode,
semantic source coverage or arbitrary M/W preservation.
The proof must query the actual pool internally, use SeededPrimaryPool's existing
InternalPrimaryCarrier reached-subset-pool law, then use actual candidate retain
facts from OriginalCandidates/OriginalCandidateInstallation. Seed equality and
candidate retain branches must both reconstruct original T including G. A
nonzero packedCheck retain witness must be normalized to original acceptance,
not silently treated as graph output1 without the internal Boolean law.

## Scope of what remains unpaid
This is plain original packed typing plus original parameter-context admission.
It is NOT arbitrary OriginalUniverseDecoder M/W preservation. Full source-universe
membership additionally requires actual window/type/annotation coverage from the
original classCodes enumeration, as well as the original bounds and context
invariants. This theorem does not alone settle that coverage, global internal
I/C or paper06 accessibility. The old raw universal target stays held. No accepted
or frozen source is modified by this fresh proposal.
