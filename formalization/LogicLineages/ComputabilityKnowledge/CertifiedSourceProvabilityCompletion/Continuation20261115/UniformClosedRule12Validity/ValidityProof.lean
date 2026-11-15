module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FullFormulaInstantiationValidity FullFormulaInstantiationValidity.ConstructorValidityTargets
open RelationalSyntaxDepthTransport
/-- Actual equality and implication scanner closure, then transport to the
literal compiled conclusion. No output validity is assumed. -/
theorem exactConclusionValidity : Targets.InternalConclusionValidity := by
 intro n p I ctx f t u
 obtain ⟨fs,fp,fc,eqtag,_,_,_,heq⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p I.fval I.h_fval
 let T := GorbowPRNumeralCalculation.Theory p
 let F := Formula.equal (LiteralSyntaxValidator.formulaCall I.fval (.succ .zero) f) (.succ .zero)
 let V := Continuation20261114.RawReflexivityDispatcher.valid I.vtag t
 let W := Continuation20261114.RawReflexivityDispatcher.valid I.vtag u
 let A := UniformClosedRule12.guards I.fval I.vtag f t u
 let G := [A]
 have hh : Hilbert.Local T ctx G (.conj (.conj F V) W) := .hypothesis List.mem_cons_self
 have hFV := Hilbert.Local.mp (.base (.logical (.andLeft (.conj F V) W))) hh
 have hW := Hilbert.Local.mp (.base (.logical (.andRight (.conj F V) W))) hh
 have hF := Hilbert.Local.mp (.base (.logical (.andLeft F V))) hFV
 have hV := Hilbert.Local.mp (.base (.logical (.andRight F V))) hFV
 obtain ⟨htSound⟩ := Continuation20261114.RawReflexivityDispatcher.TermSoundProof.sound p I.vtag I.stag I.ptag I.ctag
  I.h_vtag I.h_stag I.h_ptag I.h_ctag t
 obtain ⟨huSound⟩ := Continuation20261114.RawReflexivityDispatcher.TermSoundProof.sound p I.vtag I.stag I.ptag I.ctag
  I.h_vtag I.h_stag I.h_ptag I.h_ctag u
 have ht := Hilbert.Local.mp (.base htSound) hV
 have hu := Hilbert.Local.mp (.base huSound) hW
 have heqChildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (singleton I.ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks I.ptag (.zero : Term ctx) (.formula 0)) [t,u] :=
  .cons ⟨ht⟩ (.cons ⟨hu⟩ .nil)
 obtain ⟨hequality⟩ := ConstructorValidityProof.constructorValidity n p I.stag I.ptag I.ctag I.atag
  I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (.formula 0) .zero [t,u] heqChildren
 let leftResult := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag f t
 let rightResult := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag f u
 obtain ⟨houtputt⟩ := UniformSubstitutionFormulaValidity.StatementChecks.exactFormulaOutputValidity n p
  I.ftag I.etag I.vtag I.fval I.stepTag I.stag I.ptag I.ctag I.atag I.dtag I.len I.qtag I.ltag I.rtag
  I.h_ftag I.h_etag I.h_vtag I.h_stepTag I.h_stag I.h_ptag I.h_ctag I.h_atag I.h_dtag I.h_len I.h_qtag I.h_ltag I.h_rtag I.h_fval ctx .zero f t
 have hvalidt := Hilbert.Local.mp (Hilbert.Local.mp (.base houtputt) hV) hF
 obtain ⟨hsoundt⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) leftResult
 have hscant := Hilbert.Local.mp (.base hsoundt) hvalidt
 obtain ⟨houtputu⟩ := UniformSubstitutionFormulaValidity.StatementChecks.exactFormulaOutputValidity n p
  I.ftag I.etag I.vtag I.fval I.stepTag I.stag I.ptag I.ctag I.atag I.dtag I.len I.qtag I.ltag I.rtag
  I.h_ftag I.h_etag I.h_vtag I.h_stepTag I.h_stag I.h_ptag I.h_ctag I.h_atag I.h_dtag I.h_len I.h_qtag I.h_ltag I.h_rtag I.h_fval ctx .zero f u
 have hvalidu := Hilbert.Local.mp (Hilbert.Local.mp (.base houtputu) hW) hF
 obtain ⟨hsoundu⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) rightResult
 have hscanu := Hilbert.Local.mp (.base hsoundu) hvalidu
 have hresultChildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (singleton I.ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks I.ptag (.zero : Term ctx) (.formula 7)) [leftResult,rightResult] :=
  .cons ⟨hscant⟩ (.cons ⟨hscanu⟩ .nil)
 obtain ⟨hresults⟩ := ConstructorValidityProof.constructorValidity n p I.stag I.ptag I.ctag I.atag
  I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (.formula 7) .zero [leftResult,rightResult] hresultChildren
 let antecedent := FixedFormulaSubstitution.binaryValue I.ctag I.atag 0 t u
 let consequent := FixedFormulaSubstitution.binaryValue I.ctag I.atag 7 leftResult rightResult
 have himpChildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local T ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (singleton I.ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks I.ptag (.zero : Term ctx) (.formula 7)) [antecedent,consequent] :=
  .cons ⟨hequality⟩ (.cons ⟨hresults⟩ .nil)
 obtain ⟨himp⟩ := ConstructorValidityProof.constructorValidity n p I.stag I.ptag I.ctag I.atag
  I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (.formula 7) .zero [antecedent,consequent] himpChildren
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) (expandedConclusion I.toGraphInstallation f t u)
 have hexpanded := Hilbert.Local.mp (.base hcomplete) himp
 obtain ⟨hgraph⟩ := GraphProof.exactConclusionGraph n p I.toGraphInstallation ctx f t u
 have hA : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 have heqConclusion := Hilbert.Local.mp (.base hgraph) hA
 have hcall := LiteralRawMP.DispatcherSupportProof.callCongruence (T := T) (G := G) I.fval
  ((.zero : Term ctx) ::ᵥ compiledConclusion I.toGraphInstallation f t u ::ᵥ nil)
  ((.zero : Term ctx) ::ᵥ expandedConclusion I.toGraphInstallation f t u ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive _))
   | succ i => cases i using Fin.cases with
     | zero => exact heqConclusion
     | succ i => exact Fin.elim0 i)
 have hout := localTrans _ _ _ hcall hexpanded
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.ValidityProof
