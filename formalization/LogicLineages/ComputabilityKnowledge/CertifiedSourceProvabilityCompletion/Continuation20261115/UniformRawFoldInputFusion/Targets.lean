module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual length-driven raw-fold input fusion on arbitrary internal codes.
No validator, successful-state, native-image, exhaustion or intermediate-output
premise. All programs are fixed before runtime arguments or root tags. -/
def InternalInputFusion : Prop := ∀ n (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat),
 (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩ →
 (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ →
 (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (leftTokens rightTokens packed replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (fusion ftag atag leftTokens rightTokens packed replacement))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.Targets
