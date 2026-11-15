module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SequenceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.StackProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.MarkerProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexStepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.EnvironmentProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OutputProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Traversal
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Private membership-only interface. The expand child is recovered from step
at the final endpoint; it is NOT an added premise of the frozen target. -/
structure Installation {n : Nat} (p : Program n) where
 ftag : Nat
 ptag : Nat
 ctag : Nat
 stag : Nat
 etag : Nat
 atag : Nat
 xtag : Nat
 dtag : Nat
 ltag : Nat
 rtag : Nat
 hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩
 he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩
 hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩
 hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩
 hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩
def run {n ctx : Nat} {p : Program n} (I : Installation p) (xs : List Nat)
 (state out raw : Term ctx) : Term ctx :=
 UniformClosedSubstitutionRawFold.foldCall I.ftag (SegmentProof.tokenPrefix I.ctag xs .zero)
  (HistoryKernel.pairCall I.ptag state out) raw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Traversal
