module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.IndexProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual emitted index chunk consumes exactly the corresponding new term
task and preserves arbitrary related rest stacks. No native tail or scan premise. -/
theorem framed {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (etag vtag stag ptag ctag atag dtag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (index depth positive oldTail newTail raw : Term ctx)
 (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid vtag raw))
 (hbound : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag index (.succ depth)) (.succ positive)))
 (hrest : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (stackRelation len q l r oldTail newTail)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (resultBody stag len q l r
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 depth) newTail)
   (UniformClosedSubstitutionEmit.emitCall etag
    (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral 2) (.succ depth) oldTail) index raw)
   oldTail newTail)) := by
 obtain ⟨hi⟩ := UniformSubstitutionIndexValidity.StatementChecks.exactEmission
  n p etag vtag stag ptag ctag atag dtag he hv hs hp hc ha hd ctx index depth positive oldTail raw
 have hchunk := Hilbert.Local.mp (.mp (.base hi) hvalid) hbound
 obtain ⟨hf⟩ := FullFormulaInstantiationValidity.ConstructorFrameProof.frameOne
  p G stag ctag atag hs hc ha (LiteralSyntaxStep.taskCall ptag 0 depth)
  (UniformClosedSubstitutionEmit.emitCall etag
   (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral 2) (.succ depth) oldTail) index raw)
  newTail hchunk
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hf) hrest⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.IndexProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.IndexProof
