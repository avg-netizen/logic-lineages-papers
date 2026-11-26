module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.TermSoundProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameStatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalEqualityValidity : Targets.InternalEqualityValidity := by
 intro n p vtag ftag ptag ctag atag hv hf hp hc ha ctx raw
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p vtag hv
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p ftag hf
 let T := GorbowPRNumeralCalculation.Theory p
 let H := valid vtag raw
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let one := HistoryLookup.consCall ctag task .zero
 let two := HistoryLookup.consCall ctag task one
 let dup := HistoryAppend.appendCall atag raw raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hsound⟩ := TermSoundProof.sound p vtag stag ptag ctag hv hs hp hc raw
 have hsingle : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag one raw) (.succ .zero)) :=
  .mp (.base hsound) hh
 obtain ⟨hframe⟩ := LiteralSyntaxScan.FrameStatementChecks.exactFrame n p stag atag hs ha ctx one raw .zero one
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx one
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx task .zero one
 have hstack := Logic.trans _ _ _ hcons
  (HistoryAppend.PositiveProof.binaryCongruence ctag task task _ one (.logical (.reflexive task)) hnil)
 have hscanStack := HistoryAppend.PositiveProof.binaryCongruence stag _ two raw raw hstack (.logical (.reflexive raw))
 have htwo : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag two raw) (.succ one)) :=
  localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hscanStack))
   (localTrans _ _ _ (.mp (.base hframe) hsingle) (.base (Logic.unary (.succ (.var 0)) _ _ hnil)))
 obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two raw raw one
 have hdup : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag two dup) (.succ .zero)) :=
  localTrans _ _ _ (.mp (.base hfuse) htwo) hsingle
 obtain ⟨hequality⟩ := LiteralEqualityQuote.TermScanProof.scanEquality p stag ptag ctag hs hp hc .zero .zero dup
 have hformula := localTrans _ _ _ (.base hequality) hdup
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p ftag stag ptag ctag etag
  hf hs hp hc he .zero (RawReflexivity.equalityValue ctag atag raw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hcomplete) hformula))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.ValidityProof.internalEqualityValidity
