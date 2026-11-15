module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FullFormulaInstantiationValidity FullFormulaInstantiationValidity.ConstructorValidityTargets
open RelationalSyntaxDepthTransport
/-- Actual scanner closure of unary10 and binary7, fed by the checked uniform
output-validity theorem, then transported to the literal compiled conclusion. -/
theorem exactConclusionValidity : Targets.InternalConclusionValidity := by
 intro n p I ctx f t
 obtain ⟨fs,fp,fc,eqtag,_,_,_,heq⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p I.fval I.h_fval
 let T := GorbowPRNumeralCalculation.Theory p
 let F := Formula.equal (LiteralSyntaxValidator.formulaCall I.fval (.succ .zero) f) (.succ .zero)
 let V := Continuation20261114.RawReflexivityDispatcher.valid I.vtag t
 let A := UniformClosedInstanceRecognizer.guards I.fval I.vtag f t
 let G := [A]
 have hh : Hilbert.Local T ctx G (.conj F V) := .hypothesis List.mem_cons_self
 have hF := Hilbert.Local.mp (.base (.logical (.andLeft F V))) hh
 have hV := Hilbert.Local.mp (.base (.logical (.andRight F V))) hh
 obtain ⟨hsound⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.succ (.zero : Term ctx)) f
 have hformula := Hilbert.Local.mp (.base hsound) hF
 have hforallChildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (singleton I.ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks I.ptag (.zero : Term ctx) (.formula 10)) [f] :=
  .cons ⟨hformula⟩ .nil
 obtain ⟨hforall⟩ := ConstructorValidityProof.constructorValidity n p I.stag I.ptag I.ctag I.atag
  I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (.formula 10) .zero [f] hforallChildren
 let result := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag f t
 obtain ⟨houtput⟩ := UniformSubstitutionFormulaValidity.StatementChecks.exactFormulaOutputValidity n p
  I.ftag I.etag I.vtag I.fval I.stepTag I.stag I.ptag I.ctag I.atag I.dtag I.len I.qtag I.ltag I.rtag
  I.h_ftag I.h_etag I.h_vtag I.h_stepTag I.h_stag I.h_ptag I.h_ctag I.h_atag I.h_dtag I.h_len I.h_qtag I.h_ltag I.h_rtag I.h_fval ctx .zero f t
 have hvalidOutput := Hilbert.Local.mp (Hilbert.Local.mp (.base houtput) hV) hF
 obtain ⟨hresultSound⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) result
 have hresult := Hilbert.Local.mp (.base hresultSound) hvalidOutput
 let antecedent := HistoryLookup.consCall I.ctag (Term.numeral 10) f
 have himpChildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (singleton I.ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks I.ptag (.zero : Term ctx) (.formula 7)) [antecedent,result] :=
  .cons ⟨hforall⟩ (.cons ⟨hresult⟩ .nil)
 obtain ⟨himp⟩ := ConstructorValidityProof.constructorValidity n p I.stag I.ptag I.ctag I.atag
  I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (.formula 7) .zero [antecedent,result] himpChildren
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) (expandedConclusion I.toGraphInstallation f t)
 have hexpanded := Hilbert.Local.mp (.base hcomplete) himp
 obtain ⟨hgraph⟩ := GraphProof.exactConclusionGraph n p I.toGraphInstallation ctx f t
 have hA : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 have heqConclusion := Hilbert.Local.mp (.base hgraph) hA
 have hcall := LiteralRawMP.DispatcherSupportProof.callCongruence I.fval
  ((.zero : Term ctx) ::ᵥ compiledConclusion I.toGraphInstallation f t ::ᵥ nil)
  ((.zero : Term ctx) ::ᵥ expandedConclusion I.toGraphInstallation f t ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive _))
   | succ i => cases i using Fin.cases with
     | zero => exact heqConclusion
     | succ i => exact Fin.elim0 i)
 have hout := localTrans _ _ _ hcall hexpanded
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.ValidityProof
