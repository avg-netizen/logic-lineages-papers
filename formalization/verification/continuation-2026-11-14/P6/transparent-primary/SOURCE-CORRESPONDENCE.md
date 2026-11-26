# Concrete primary-list installation design (not proved/frozen yet)

Source correspondence: MembershipDefinitions.listValue uses decodedValue on the
original context and Object decoders, followed by rawPackedDecode with Object
Gamma and value. All three failure cases yield zero. A successful q produces
entriesCode of the literal ContextUniformPrimary.primaryList. The latter runs
literal step with the fixed vertices pool for exactly vertices.length rounds.

Proposed new AST, with T,C,P : Program 2 and E : Program 3:

  L(T,C,P,E) = branch T zero
    (composition (PrimaryIteration.run E) [C,P,projection 0,projection 1])

The branch tests original T (Boolean native calibration), NOT universe/source
membership. In accepted inputs the input numeric seed equals Encodable.encode q
by the already proved original packed reencoding. In rejected/malformed inputs
L returns the original nil code zero, regardless of C/P/E outputs.

Choose C and P with allPrimitiveFunctions from explicit numeric functions
obtained by replacing primaryList in listValue respectively with
vertices.length and entriesCode(vertices). These PR proofs reuse
ContextUniformPrimaryPrimitiveProof.verticesPrimitive and
MembershipLeafSelectionProof.entriesPrimitive, preserving all original codecs.

E uses the ORIGINAL context decoder on unpair(parameter).1 and ordinary
Encodable.decode (RawPacked n) on its two numeric operands, then
packedCodeExchange arity ctx.symbols ctx.types; failure returns zero.
The plain structural Encodable decoder (not typed rawPackedDecode) is needed
here so the earlier OriginalPrimaryCalibration's all-RawPacked edge condition
holds, including untyped raw pairs. Its PR proof uses Primrec.decode and
ContextUniformPrimaryPrimitiveProof.packedExchangePrimitive. It does NOT
supply or assume any internal edge correctness.

Intended exact contracts:
1. Unconditional existence of C/P/E with explicit all-vector numeric
   calibrations (not merely premises asserting them).
2. For arbitrary T with target calibration, chosen C/P/E give ListCalibrated
   for this exact L on ALL vectors, malformed defaults included.
3. For arbitrary T,C,P,E, actual internal T(seed,param)=1 and actual
   L(out,seed,param) imply contains(out,seed)=1. Query C/P, recover selected
   run graph, and use arbitrary-count InternalSeedMembership. No calibration
   or semantic correctness premise occurs in this internal law.
4. For arbitrary T,C,P,E, actual T(seed,param)=1 implies the actual
   Membership.classTest T L (TransparentCandidate.candidate T) accepts
   (seed,seed,param). Query L and use contract3 plus CandidateIntegration's
   existing factor. This removes opaque L as a blocker to class reflexivity.

Then retain the complete Package/rank tuple through CandidateIntegration's
RetainedTuple. This does not establish internal class symmetry/coherence,
exchange correctness, decoder transport, source stability, or full paper06 I/C.
