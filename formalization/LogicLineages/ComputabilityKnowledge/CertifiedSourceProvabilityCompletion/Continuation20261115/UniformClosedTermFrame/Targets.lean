module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Entire actual length-driven raw fold, not its output projection. Only the
original closed-term validator guards tokens; replacement, bound, rest and out
are arbitrary internal codes. No native image, successful intermediate step,
frame-helper membership or well-formed-rest premise is permitted. -/
def InternalFramedClosedIdentity : Prop := ∀ n (p : Program n)
 (ftag etag vtag stepTag stag ptag ctag atag dtag len q l r : Nat),
 (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩ →
 (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩ →
 (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (tokens bound rest out replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Continuation20261114.RawReflexivityDispatcher.valid vtag tokens)
   (.equal (UniformClosedSubstitutionRawFold.foldCall ftag tokens
     (initial ptag ctag bound rest out) replacement)
    (final ptag atag rest out tokens))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Targets
