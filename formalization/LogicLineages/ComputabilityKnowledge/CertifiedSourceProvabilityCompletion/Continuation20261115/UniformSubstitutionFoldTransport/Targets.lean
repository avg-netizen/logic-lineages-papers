module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Success-directed actual raw-fold composition. Original scan success, not a
native token-list image or intermediate-success premise, must justify every
old step internally. No frame-helper AST membership or output-validity premise. -/
def InternalSuccessfulFoldTransport : Prop := ∀ n (p : Program n)
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
 ∀ ctx (tokens oldTasks newTasks oldResult raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Continuation20261114.RawReflexivityDispatcher.valid vtag raw)
   (.imp (UniformSubstitutionChunkTransport.stackRelation len q l r oldTasks newTasks)
    (.imp (.equal (LiteralSyntaxScan.scanCall stag oldTasks tokens) (.succ oldResult))
     (UniformSubstitutionChunkTransport.results stag len q l r newTasks
      (output ftag ptag r tokens oldTasks raw) oldResult)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.Targets
