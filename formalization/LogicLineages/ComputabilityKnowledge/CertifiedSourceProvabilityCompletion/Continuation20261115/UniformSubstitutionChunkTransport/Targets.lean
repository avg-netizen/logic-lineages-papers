module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- One genuine emitted chunk simulates an arbitrary successful original
syntax step. All constructor/index cases and arbitrary related-tail recovery
are proof duties, not premises. Failure/NONE cases are excluded only by the
actual old-success premise; old depth zero is excluded by the stack relation. -/
def InternalChunkTransport : Prop := ∀ n (p : Program n)
 (etag vtag stepTag stag ptag ctag atag dtag len q l r : Nat),
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
 ∀ ctx (oldTasks newTasks token oldResult raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Continuation20261114.RawReflexivityDispatcher.valid vtag raw)
   (.imp (stackRelation len q l r oldTasks newTasks)
    (.imp (.equal (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token) (.succ oldResult))
     (results stag len q l r newTasks
      (UniformClosedSubstitutionEmit.emitCall etag (.succ oldTasks) token raw) oldResult)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Targets
