module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ScanProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TaskProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.MarkerProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Suppressed variable marker: new scanner consumes empty chunk and preserves
its whole pending term, while old syntax has advanced to the pending index. -/
theorem marker {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (etag stag ptag ctag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (depth oldTail newTail raw : Term ctx)
 (hrest : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r oldTail newTail)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (resultBody stag len q l r
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 depth) newTail)
   (UniformClosedSubstitutionEmit.emitCall etag
    (UniformClosedSubstitutionEmit.stateValue ptag ctag .zero (.succ depth) oldTail) .zero raw)
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 2 (.succ depth)) oldTail)
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 depth) newTail))) := by
 let newTasks := HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 depth) newTail
 obtain ⟨hemit⟩ := UniformClosedSubstitutionEmit.NonIndexProof.marker p etag ptag ctag he hp hc (.succ depth) oldTail raw
 have heq := UniformSubstitutionIndexValidity.BranchProof.scanCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := G) stag newTasks _ _ (.base hemit)
 obtain ⟨hnil⟩ := ScanProof.nil p stag ptag hs hp newTasks
 have hscan := localTrans _ _ _ heq (.base hnil)
 obtain ⟨htask⟩ := TaskProof.index p G ptag l r hp hl hr depth
 obtain ⟨hcons⟩ := ConsProof.consRelated p len q l r ctag hlen hq hc
  (LiteralSyntaxStep.taskCall ptag 2 (.succ depth)) oldTail (LiteralSyntaxStep.taskCall ptag 0 depth) newTail
 have hrel := Hilbert.Local.mp (.base hcons) (.mp (.mp (.base (.logical (.andIntro _ _))) htask) hrest)
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hscan) hrel⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.MarkerProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.MarkerProof
