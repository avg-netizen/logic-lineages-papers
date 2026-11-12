module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualSpinePrefix : OriginalApplicationSpinePrefixTargets.ActualSpinePrefix := by
 intro body alpha Delta s t cert childCert parameter fn targetFn arg d e arrow har hfl htl hal hs ht hg
 let f : Program 2 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 0)
 let g : Program 2 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 1)
 let sf : Program 2 := leftOf f
 let tf : Program 2 := leftOf g
 let sd : Program 2 := rightOf f
 let td : Program 2 := rightOf g
 let sn : Program 2 := .composition .succ (fun _ : Fin 1 => sd)
 let tn : Program 2 := .composition .succ (fun _ : Fin 1 => td)
 let qs : Fin 8 → Program 2 := ![f,g,sf,tf,sd,td,pairOf sf sn,pairOf tf tn]
 let xs : Fin 2 → OTerm alpha := ![fn,targetFn]
 apply queryCases qs xs _
 intro beta j ys Theta incl hq
 simp only [graph4Rename,numeralRename]
 have har' := renameInto har j Theta incl
 have hfl' := renameInto hfl j Theta incl
 have htl' := renameInto htl j Theta incl
 have hal' := renameInto hal j Theta incl
 have hs' := renameInto hs j Theta incl
 have ht' := renameInto ht j Theta incl
 have hg' := renameInto hg j Theta incl
 simp only [graph1Rename,graph2Rename,graph4Rename,numeralRename] at har' hfl' htl' hal' hs' ht' hg'
 let xx : Fin 2 → OTerm beta := ![fn.relabel j,targetFn.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
  funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have hq' (i : Fin 8) : Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
  simpa only [hx] using hq i
 have hfm := unaryRecover BottomSpineMeasure.measure (.projection 0) (ys 0) (fn.relabel j) xx (hq' 0) (projectionValue 0 xx)
 have htm := unaryRecover BottomSpineMeasure.measure (.projection 1) (ys 1) (targetFn.relabel j) xx (hq' 1) (projectionValue 1 xx)
 have hsf := unaryRecover InternalUnpair.left f (ys 2) (ys 0) xx (hq' 2) (hq' 0)
 have htf := unaryRecover InternalUnpair.left g (ys 3) (ys 1) xx (hq' 3) (hq' 1)
 have hsd := unaryRecover InternalUnpair.right f (ys 4) (ys 0) xx (hq' 4) (hq' 0)
 have htd := unaryRecover InternalUnpair.right g (ys 5) (ys 1) xx (hq' 5) (hq' 1)
 have hsn : Nonempty (Derivation body Theta (graph1 Program.succ (suc (ys 4)) (ys 4))) := successorValue ![ys 4]
 have htn : Nonempty (Derivation body Theta (graph1 Program.succ (suc (ys 5)) (ys 5))) := successorValue ![ys 5]
 have hsn' := unaryValue Program.succ sd (suc (ys 4)) (ys 4) xx hsn (hq' 4)
 have htn' := unaryValue Program.succ td (suc (ys 5)) (ys 5) xx htn (hq' 5)
 have hp := binaryRecover InternalPairing.pairing sf sn (ys 6) (ys 2) (suc (ys 4)) xx (hq' 6) (hq' 2) hsn'
 have hqp := binaryRecover InternalPairing.pairing tf tn (ys 7) (ys 3) (suc (ys 5)) xx (hq' 7) (hq' 3) htn'
 have hpm := OriginalFinalVariableCanonicalSupportProof.iffBackward (SpineApplicationRawProof.rawEquation (arrow.relabel j) (d.relabel j) (e.relabel j)
  (fn.relabel j) (arg.relabel j) (s.relabel j) (ys 0) (ys 2) (ys 4) (suc (ys 4)) (ys 6)
  har' hfl' hal' hs' hfm hsf hsd hsn) hp
 have hqm := OriginalFinalVariableCanonicalSupportProof.iffBackward (SpineApplicationRawProof.rawEquation (arrow.relabel j) (d.relabel j) (e.relabel j)
  (targetFn.relabel j) (arg.relabel j) (t.relabel j) (ys 1) (ys 3) (ys 5) (suc (ys 5)) (ys 7)
  har' htl' hal' ht' htm htf htd htn) hqp
 exact OriginalApplicationSpinePrefixCoreProof.atMarks (s.relabel j) (t.relabel j) (cert.relabel j)
  (childCert.relabel j) (parameter.relabel j) (fn.relabel j) (targetFn.relabel j)
  (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7)
  hfm htm hsf htf hsd htd hpm hqm hp hqp hg'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixProof
