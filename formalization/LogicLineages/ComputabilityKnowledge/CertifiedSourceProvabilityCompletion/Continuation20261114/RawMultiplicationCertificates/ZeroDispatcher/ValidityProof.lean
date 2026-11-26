module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationCertificates.ZeroDispatcher.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationCertificates.ZeroDispatcher.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalFormulaValidity : Targets.InternalFormulaValidity := by
 intro n p vtag ftag ptag ctag atag hv hf hp hc ha ctx raw
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p vtag hv
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p ftag hf
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let one := HistoryLookup.consCall ctag task .zero
 let two := HistoryLookup.consCall ctag task one
 let three := HistoryLookup.consCall ctag task two
 let zr := HistoryLookup.consCall ctag (.succ (.zero : Term ctx)) .zero
 let arg := HistoryAppend.appendCall atag raw zr
 let ar := HistoryLookup.consCall ctag (Term.numeral 4) arg
 let dup := HistoryAppend.appendCall atag ar zr
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hraw3⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha raw two
 obtain ⟨hzero⟩ := LiteralNumeralPrefix.TermScanProof.scanZero p stag ptag ctag hs hp hc .zero one
 obtain ⟨hfuse1⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx three raw zr two
 have harg : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag three arg) (.succ one)) :=
  localTrans _ _ _ (.mp (.base hfuse1) (.mp (.base hraw3) hh)) (.base hzero)
 obtain ⟨hadd⟩ := LiteralTemplateQuote.TermScanProof.scanMul p stag ptag ctag hs hp hc .zero one arg
 have har : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag two ar) (.succ one)) :=
  localTrans _ _ _ (.base hadd) harg
 obtain ⟨hzero1⟩ := LiteralNumeralPrefix.TermScanProof.scanZero p stag ptag ctag hs hp hc .zero .zero
 obtain ⟨hfuse2⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two ar zr one
 have hdup : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag two dup) (.succ .zero)) :=
  localTrans _ _ _ (.mp (.base hfuse2) har) (.base hzero1)
 obtain ⟨hequality⟩ := LiteralEqualityQuote.TermScanProof.scanEquality p stag ptag ctag hs hp hc .zero .zero dup
 have hformula := localTrans _ _ _ (.base hequality) hdup
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p ftag stag ptag ctag etag
  hf hs hp hc he .zero (RawMultiplication.Zero.equalityValue ctag atag raw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hcomplete) hformula))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationCertificates.ZeroDispatcher.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationCertificates.ZeroDispatcher.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationCertificates.ZeroDispatcher.ValidityProof.internalFormulaValidity
