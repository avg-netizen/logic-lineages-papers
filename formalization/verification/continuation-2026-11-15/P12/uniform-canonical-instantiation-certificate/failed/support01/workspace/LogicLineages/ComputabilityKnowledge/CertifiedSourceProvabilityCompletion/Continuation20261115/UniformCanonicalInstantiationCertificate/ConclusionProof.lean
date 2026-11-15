module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.TemplateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.ConclusionProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPRDefiningEquations List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
/-- Exact actual compiled conclusion, for a formula chosen after installation. -/
theorem canonical {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x) (f : Formula 1)
 {ctx : Nat} (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Continuation20261114.RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (UniformClosedRule13.conclusionValue I.caseTag I.predTag I.ctag
    (Term.numeral (FullFormulaInstantiation.templateCode f)) raw)
    (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := Continuation20261114.RawReflexivityDispatcher.valid I.vtag raw
 let G := [A]
 let template := Term.numeral (n := ctx) (FullFormulaInstantiation.templateCode f)
 have ha : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨htemplate⟩ := TemplateProof.validTemplate p old arithmetic x I f ctx
 have hg : Hilbert.Local T ctx G (UniformClosedInstanceRecognizer.guards I.fval I.vtag template raw) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.base htemplate)) ha
 obtain ⟨hgraph⟩ := UniformClosedRule13Validity.GraphProof.exactConclusionGraph n p
  I.toDispatcherInstallation.toInstallation.toGraphInstallation ctx template raw
 have hc := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hgraph) hg
 obtain ⟨hag⟩ := UniformFixedFormulaAgreement.StatementChecks.exactAgreement n p
  I.ftag I.etag I.vtag I.fval I.stepTag I.stag I.ptag I.ctag I.atag I.dtag I.len I.qtag I.ltag I.rtag
  I.h_ftag I.h_etag I.h_vtag I.h_stepTag I.h_stag I.h_ptag I.h_ctag I.h_atag I.h_dtag
  I.h_len I.h_qtag I.h_ltag I.h_rtag I.h_fval f ctx raw
 have hi := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hag) ha
 let antecedent := HistoryLookup.consCall I.ctag (Term.numeral (n := ctx) 10) template
 let output := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag template raw
 let instanceValue := FullFormulaInstantiation.instanceValue I.ctag I.atag f raw
 have happ : Hilbert.Local T ctx G
  (.equal (HistoryAppend.appendCall I.atag antecedent output)
   (HistoryAppend.appendCall I.atag antecedent instanceValue)) := by
  apply callCongruence (T := T) (G := G) I.atag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive antecedent))
  | succ i => cases i using Fin.cases with
    | zero => exact hi
    | succ i => exact Fin.elim0 i
 have hshape : Hilbert.Local T ctx G
  (.equal (HistoryLookup.consCall I.ctag (Term.numeral 7) (HistoryAppend.appendCall I.atag antecedent output))
   (HistoryLookup.consCall I.ctag (Term.numeral 7) (HistoryAppend.appendCall I.atag antecedent instanceValue))) := by
  apply callCongruence (T := T) (G := G) I.ctag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive _))
  | succ i => cases i using Fin.cases with
    | zero => exact happ
    | succ i => exact Fin.elim0 i
 exact ⟨(localTrans _ _ _ hc hshape).discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.ConclusionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.ConclusionProof
