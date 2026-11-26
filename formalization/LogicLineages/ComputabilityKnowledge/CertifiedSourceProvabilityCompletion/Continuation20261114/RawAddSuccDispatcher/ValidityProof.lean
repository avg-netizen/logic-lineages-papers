module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccDispatcher.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccDispatcher.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalFormulaValidity : Targets.InternalFormulaValidity := by
 intro n p vtag ftag ptag ctag atag hv hf hp hc ha ctx raw rawB
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p vtag hv
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p ftag hf
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let K := RawReflexivityDispatcher.valid vtag rawB
 let G := [K,H]
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let one := HistoryLookup.consCall ctag task .zero
 let two := HistoryLookup.consCall ctag task one
 let three := HistoryLookup.consCall ctag task two
 let sr := HistoryLookup.consCall ctag (Term.numeral 2) rawB
 let arg := HistoryAppend.appendCall atag raw sr
 let ar := HistoryLookup.consCall ctag (Term.numeral 3) arg
 let abArg := HistoryAppend.appendCall atag raw rawB
 let ab := HistoryLookup.consCall ctag (Term.numeral 3) abArg
 let sab := HistoryLookup.consCall ctag (Term.numeral 2) ab
 let dup := HistoryAppend.appendCall atag ar sab
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hk : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 obtain ⟨hraw3⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha raw two
 obtain ⟨hb2⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha rawB one
 obtain ⟨hsr⟩ := LiteralNumeralPrefix.TermScanProof.scanSucc p stag ptag ctag hs hp hc .zero one rawB
 have hsrScan : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag two sr) (.succ one)) :=
  localTrans _ _ _ (.base hsr) (.mp (.base hb2) hk)
 obtain ⟨hfuse1⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx three raw sr two
 have harg : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag three arg) (.succ one)) :=
  localTrans _ _ _ (.mp (.base hfuse1) (.mp (.base hraw3) hh)) hsrScan
 obtain ⟨hadd⟩ := LiteralTemplateQuote.TermScanProof.scanAdd p stag ptag ctag hs hp hc .zero one arg
 have har : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag two ar) (.succ one)) :=
  localTrans _ _ _ (.base hadd) harg
 obtain ⟨ha2⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha raw one
 obtain ⟨hb1⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha rawB .zero
 obtain ⟨hfuseAB⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two raw rawB one
 have habArg : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag two abArg) (.succ .zero)) :=
  localTrans _ _ _ (.mp (.base hfuseAB) (.mp (.base ha2) hh)) (.mp (.base hb1) hk)
 obtain ⟨haddAB⟩ := LiteralTemplateQuote.TermScanProof.scanAdd p stag ptag ctag hs hp hc .zero .zero abArg
 have hab : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag one ab) (.succ .zero)) :=
  localTrans _ _ _ (.base haddAB) habArg
 obtain ⟨hsab⟩ := LiteralNumeralPrefix.TermScanProof.scanSucc p stag ptag ctag hs hp hc .zero .zero ab
 have hsabScan : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag one sab) (.succ .zero)) :=
  localTrans _ _ _ (.base hsab) hab
 obtain ⟨hfuse2⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two ar sab one
 have hdup : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag two dup) (.succ .zero)) :=
  localTrans _ _ _ (.mp (.base hfuse2) har) hsabScan
 obtain ⟨hequality⟩ := LiteralEqualityQuote.TermScanProof.scanEquality p stag ptag ctag hs hp hc .zero .zero dup
 have hformula := localTrans _ _ _ (.base hequality) hdup
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p ftag stag ptag ctag etag
  hf hs hp hc he .zero (RawAddSucc.equalityValue ctag atag raw rawB)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base hcomplete) hformula)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccDispatcher.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccDispatcher.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccDispatcher.ValidityProof.internalFormulaValidity
