module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.AntecedentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalFormulaValidity : Targets.InternalFormulaValidity := by
 intro a b n p vtag ftag ptag ctag atag hv hf hp hc ha ctx raw
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p vtag hv
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p ftag hf
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let G := [H]
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let one := HistoryLookup.consCall ctag task .zero
 let two := HistoryLookup.consCall ctag task one
 let fs := LiteralSyntaxValidator.QuantifierOperationalProof.tasks ptag ctag (.zero : Term ctx)
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let av := RawUnarySubstitution.value ctag atag raw a
 let bv := RawUnarySubstitution.value ctag atag raw b
 obtain ⟨haScan⟩ := RawUnarySubstitutionValidity.StatementChecks.exactScan a n p vtag stag ptag ctag atag hv hs hp hc ha ctx raw one
 obtain ⟨hbScan⟩ := RawUnarySubstitutionValidity.StatementChecks.exactScan b n p vtag stag ptag ctag atag hv hs hp hc ha ctx raw .zero
 obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two av bv one
 have hab := localTrans _ _ _ (.mp (.base hfuse) (.mp (.base haScan) hh)) (.mp (.base hbScan) hh)
 obtain ⟨heq⟩ := LiteralEqualityQuote.TermScanProof.scanEquality p stag ptag ctag hs hp hc .zero .zero (HistoryAppend.appendCall atag av bv)
 have hinstance : Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall stag fs (RawEqualityInstantiation.instanceValue ctag atag a b raw)) (.succ .zero)) :=
  localTrans _ _ _ (.base heq) hab
 let antecedent := HistoryLookup.consCall ctag (Term.numeral 10) (Term.numeral (RawEqualityInstantiation.templateCode a b))
 obtain ⟨hant⟩ := AntecedentProof.antecedent (ctx := ctx) a b p ftag ctag hf hc
 obtain ⟨hsound⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p ftag stag ptag ctag etag hf hs hp hc he .zero antecedent
 have hantecedent : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs antecedent) (.succ .zero)) :=
  .base (.mp hsound hant)
 have scanImp (a b : Term ctx)
  (hA : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs a) (.succ .zero)))
  (hB : Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs b) (.succ .zero))) :
  Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag fs (RawUniversalReplace.binaryValue ctag atag 7 a b)) (.succ .zero)) := by
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

 have hformula := scanImp antecedent (RawEqualityInstantiation.instanceValue ctag atag a b raw) hantecedent hinstance
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p ftag stag ptag ctag etag
  hf hs hp hc he .zero (RawEqualityInstantiation.formulaValue ctag atag a b raw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hcomplete) hformula))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.ValidityProof.internalFormulaValidity
