module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightAcceptance
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113
/-- Literal prefix of the ORIGINAL phi=((t*v)=(x*v)): [0] ++ (t*v)
++ [4,0,0]. Appending v must reproduce phi exactly; no replacement encoding. -/
def prefixValue {ctx : Nat} (ctag atag : Nat) (t v : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero
  (HistoryAppend.appendCall atag (RawMulRightReplace.binaryValue ctag atag 4 t v)
   (HistoryLookup.consCall ctag (Term.numeral 4)
    (HistoryLookup.consCall ctag .zero (HistoryLookup.consCall ctag .zero .zero))))
structure Installation {n : Nat} (p : Program n) (old : Program 1) extends
 toOccurrence : RawSuffixOccurrence.Installation p RawMulRightReplace.candidateTest where
 qtag : Nat
 logicalTag : Nat
 pairTag : Nat
 validatorTag : Nat
 leftDecoderTag : Nat
 rightDecoderTag : Nat
 hq : (nodes p)[qtag]? = some ⟨3,RawMulRightReplace.lineConstructor⟩
 hlogical : (nodes p)[logicalTag]? = some ⟨1,RawMulRightReplace.logicalLeaf old⟩
 hp : (nodes p)[pairTag]? = some ⟨2,HistoryCodec.pair⟩
 hv : (nodes p)[validatorTag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
 hleft : (nodes p)[leftDecoderTag]? = some ⟨1,HistoryDecoder.decoder false⟩
 hright : (nodes p)[rightDecoderTag]? = some ⟨1,HistoryDecoder.decoder true⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightAcceptance
