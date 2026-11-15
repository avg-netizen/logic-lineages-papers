module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.BoundProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ScanProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.OutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport InvariantProof BoundProof
open UniformSubstitutionChunkTransport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual accumulator step: chunk scan composes with prefix scan by original
append fusion, then genuine tail IH consumes the new relation and old success. -/
theorem consAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (ftag etag vtag stepTag stag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (token tokens start raw oldTasks current out oldResult nextOld nextNew : Term ctx)
 (hih : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (allStates ftag vtag stag ptag len q l r tokens start raw))
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid vtag raw))
 (hpref : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag start out) (.succ current)))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag oldTasks (HistoryLookup.consCall ctag token tokens)) (.succ oldResult)))
 (hstepResult : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token) (.succ nextOld)))
 (hchunk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (resultBody stag len q l r current
   (UniformClosedSubstitutionEmit.emitCall etag (.succ oldTasks) token raw) nextOld nextNew)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (results stag len q l r start
   (outputAt ftag ptag r (HistoryLookup.consCall ctag token tokens) oldTasks out raw) oldResult)) := by
 let chunk := UniformClosedSubstitutionEmit.emitCall etag (.succ oldTasks) token raw
 let nextOut := HistoryAppend.appendCall atag out chunk
 have hscan := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hchunk
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hchunk
 obtain ⟨hfusion⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx start out chunk current
 have hprefix := localTrans _ _ _ (Hilbert.Local.mp (.base hfusion) hpref) hscan
 obtain ⟨hcons⟩ := ScanProof.cons p G stag stepTag ptag ctag hs hstep hp hc token tokens oldTasks nextOld hstepResult
 have htail := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hcons) hold
 have hi := Hilbert.Local.mp (.base (instanceRule ftag vtag stag ptag len q l r tokens start raw nextOld nextNew nextOut oldResult)) hih
 have hout := Hilbert.Local.mp (.mp (.mp (.mp hi hv) hrel) hprefix) htail
 obtain ⟨heq⟩ := OutputProof.advance p G ftag etag stepTag ptag ctag atag r hf he hstep hp hc ha
  token tokens oldTasks nextOld out raw hstepResult
 exact ⟨.mp (.mp (.base (UniformSubstitutionChunkTransport.NewStackProof.transportChunk stag len q l r start
  (outputAt ftag ptag r tokens nextOld nextOut raw)
  (outputAt ftag ptag r (HistoryLookup.consCall ctag token tokens) oldTasks out raw) oldResult))
  (HistoryOrder.StepProof.localSym _ _ heq)) hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ConsProof
