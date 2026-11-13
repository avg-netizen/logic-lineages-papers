module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Construct the replacement prefix of a literal scheduled visit. -/
theorem scheduledSuffixCases (prefix suffix rest frame tagged returnRest next : OTerm alpha) (psi : Formula alpha)
 (hrest : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append rest prefix suffix)))
 (hret : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode returnRest frame rest)))
 (hnext : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append next tagged returnRest)))
 (consume : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (newPrefix : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append
     (next.relabel j) newPrefix (suffix.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let p : Program 4 := consOf (.projection 0) (.projection 1)
 let q : Program 4 := .composition InternalApplicationValidityStackAppend.append ![.projection 2,p]
 let r : Program 4 := .composition InternalApplicationValidityStackAppend.append ![q,.projection 3]
 let qs : Fin 3 → Program 4 := ![p,q,r]
 let xs : Fin 4 → OTerm alpha := Fin.cons frame (Fin.cons prefix (Fin.cons tagged (Fin.cons suffix Fin.elim0)))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hinc hq
 let xx : Fin 4 → OTerm beta := Fin.cons (frame.relabel j) (Fin.cons (prefix.relabel j)
   (Fin.cons (tagged.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)))
 have hxs : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 rw [hxs] at hq
 have hp := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
   (ys 0) (frame.relabel j) (prefix.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have hab := binaryRecover InternalApplicationValidityStackAppend.append (.projection 2) p
   (ys 1) (tagged.relabel j) (ys 0) xx (hq 1) (projectionValue 2 xx) (hq 0)
 have hout := binaryRecover InternalApplicationValidityStackAppend.append q (.projection 3)
   (ys 2) (ys 1) (suffix.relabel j) xx (hq 2) (hq 1) (projectionValue 3 xx)
 have hrest' := renameInto hrest j Theta hinc
 have hret' := renameInto hret j Theta hinc
 have hnext' := renameInto hnext j Theta hinc
 simp only [graph2Rename] at hrest' hret' hnext'
 have hbc := InternalApplicationValidityStackAppendListProof.consBackward
   (ys 0) (frame.relabel j) (prefix.relabel j) (suffix.relabel j) (rest.relabel j) (returnRest.relabel j)
   hp hrest' hret'
 have hright := AppendReassociationProof.appendReassociation body beta Theta
   (tagged.relabel j) (ys 0) (suffix.relabel j) (ys 1) (returnRest.relabel j) (ys 2) hab hbc hout
 have he := valueUnique InternalApplicationValidityStackAppend.append (ys 2) (next.relabel j)
   (Fin.cons (tagged.relabel j) (Fin.cons (returnRest.relabel j) Fin.elim0)) hright hnext'
 exact consume beta j Theta (ys 1) hinc
   (outputTransport InternalApplicationValidityStackAppend.append (ys 2) (next.relabel j)
     (Fin.cons (ys 1) (Fin.cons (suffix.relabel j) Fin.elim0)) he hout)

theorem protectedVisitCases : ProtectedAgendaTargets.ProtectedVisitCases := by
 intro R body alpha Delta input work results visit rest parent jobs prefix suffix psi hs hw hv he ha consume
 apply OriginalHereditaryInternalVisitProof.visitCases R body alpha Delta
   input work results visit rest parent jobs psi hs hw hv he
 intro beta j Theta childCount deletionCount counts payload returnFrame tagged returnRest next out
   hinc _ _ _ hpayload hreturn _ hreturnRest hscheduled hout hstep
 have ha' := renameInto ha j Theta hinc
 rw [graph2Rename] at ha'
 apply scheduledSuffixCases (prefix.relabel j) (suffix.relabel j) (rest.relabel j)
   returnFrame tagged returnRest next (psi.relabel j) ha' hreturnRest hscheduled
 intro gamma k Xi newPrefix hk hprotected
 have hpayload' := renameInto hpayload k Xi hk
 have hreturn' := renameInto hreturn k Xi hk
 have hout' := renameInto hout k Xi hk
 have hstep' := renameInto hstep k Xi hk
 simp only [graph1Rename,graph2Rename,numeralRename] at hpayload' hreturn' hout' hstep'
 have hresult := consume gamma (k ∘ j) Xi (counts.relabel k) (payload.relabel k) (returnFrame.relabel k)
   newPrefix (next.relabel k) (out.relabel k)
   (by
     intro f hf
     simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk _ (hinc f hf))
   (by simpa only [Term.relabel_relabel] using hpayload')
   hreturn'
   (by simpa only [Term.relabel_relabel] using hprotected)
   (by simpa only [Term.relabel_relabel] using hout')
   (by simpa only [Term.relabel_relabel] using hstep')
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hresult
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaProof
