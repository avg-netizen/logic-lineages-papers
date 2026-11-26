module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher.ValidityProof
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
 let fs := LiteralSyntaxValidator.QuantifierOperationalProof.tasks ptag ctag (.zero : Term ctx)
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hk : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 have scanA (rest : Term ctx) : Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag task rest) raw) (.succ rest)) := by
  apply Classical.choice
  obtain ⟨h⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha raw rest
  exact ⟨.mp (.base h) hh⟩
 have scanB (rest : Term ctx) : Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag task rest) rawB) (.succ rest)) := by
  apply Classical.choice
  obtain ⟨h⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha rawB rest
  exact ⟨.mp (.base h) hk⟩
 have scanSucc (a rest : Term ctx)
  (h : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag task rest) a) (.succ rest))) :
  Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag task rest) (RawSuccReplace.succValue ctag a)) (.succ rest)) := by
  apply Classical.choice
  obtain ⟨heq⟩ := LiteralNumeralPrefix.TermScanProof.scanSucc p stag ptag ctag hs hp hc .zero rest a
  exact ⟨localTrans _ _ _ (.base heq) h⟩
 have scanEq (a b : Term ctx)
  (hA : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag two a) (.succ one)))
  (hB : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag one b) (.succ .zero))) :
  Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs (RawSuccReplace.binaryValue ctag atag 0 a b)) (.succ .zero)) := by
  apply Classical.choice
  obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two a b one
  have hj := localTrans _ _ _ (.mp (.base hfuse) hA) hB
  obtain ⟨heq⟩ := LiteralEqualityQuote.TermScanProof.scanEquality p stag ptag ctag hs hp hc .zero .zero (HistoryAppend.appendCall atag a b)
  exact ⟨localTrans _ _ _ (.base heq) hj⟩
 have scanImp (a b : Term ctx)
  (hA : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs a) (.succ .zero)))
  (hB : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs b) (.succ .zero))) :
  Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs (RawSuccReplace.binaryValue ctag atag 7 a b)) (.succ .zero)) := by
  apply Classical.choice
  obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
  obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
  obtain ⟨expandTag,hexpand⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stepTag hstep
  let ds := LiteralSyntaxValidator.ImplicationOperationalProof.doubleTasks ptag ctag (.zero : Term ctx)
  obtain ⟨hpref⟩ := LiteralSyntaxValidator.ImplicationOperationalProof.doubledPrefix p stag atag ptag ctag hs ha hc .zero a
  have hprefix := Hilbert.Local.mp (.base hpref) hA
  obtain ⟨hstepEq⟩ := LiteralSyntaxValidator.ImplicationOperationalProof.implicationStep p stepTag expandTag atag ptag ctag hstep hexpand ha hp hc .zero
  obtain ⟨hunroll⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.scanConsSuccess p stag itag ltag ptag rtag ctag stepTag hs hi hl hp hr hc hstep
   fs ds (Term.numeral 7) (HistoryAppend.appendCall atag a b)
  obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx ds a b fs
  exact ⟨localTrans _ _ _ (.base (.mp hunroll hstepEq))
   (localTrans _ _ _ (.mp (.base hfuse) hprefix) hB)⟩
 have heq := scanEq raw rawB (scanA one) (scanB .zero)
 have hself := scanEq (RawSuccReplace.succValue ctag raw) (RawSuccReplace.succValue ctag raw)
  (scanSucc raw one (scanA one)) (scanSucc raw .zero (scanA .zero))
 have hcong := scanEq (RawSuccReplace.succValue ctag raw) (RawSuccReplace.succValue ctag rawB)
  (scanSucc raw one (scanA one)) (scanSucc rawB .zero (scanB .zero))
 have hinner := scanImp _ _ hself hcong
 have hformula := scanImp _ _ heq hinner
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p ftag stag ptag ctag etag
  hf hs hp hc he .zero (RawSuccReplace.formulaValue ctag atag raw rawB)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base hcomplete) hformula)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher.ValidityProof.internalFormulaValidity
