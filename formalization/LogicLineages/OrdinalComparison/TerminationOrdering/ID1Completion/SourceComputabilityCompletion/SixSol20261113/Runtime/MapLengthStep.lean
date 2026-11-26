module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildMapRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionStep
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthStep
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open MapLengthSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem consCore (F : Program 1) (size jobs head tail tagged : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row F size)))
 (hf : Nonempty (Derivation body Delta (fields F (suc size) jobs tagged)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs head tail))) :
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc size) tagged)) := by
 have hl := OriginalContextInsertionSupportProof.successorLengthTail jobs head tail size hc (andLeft hf)
 let tp : Program 2 := .composition (InternalListMap.map (k := 0) F) (fun _ : Fin 1 => .projection 1)
 let vp : Program 2 := .composition F (fun _ : Fin 1 => .projection 0)
 let qs : Fin 2 → Program 2 := ![tp,vp]
 let xs : Fin 2 → OTerm alpha := ![head,tail]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hq
 let xx : Fin 2 → OTerm beta := ![head.relabel j,tail.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hl' := renameInto hl j Theta hinc
 simp only [rowRename,fieldsRename,sucRelabel,graph2Rename,OriginalContextInsertionSyntaxProof.lengthRename] at hi' hf' hc' hl'
 have hmap := unaryRecover (InternalListMap.map (k := 0) F) (.projection 1) (ys 0) (tail.relabel j) xx (hq 0) (projectionValue 1 xx)
 have hv := unaryRecover F (.projection 0) (ys 1) (head.relabel j) xx (hq 1) (projectionValue 0 xx)
 have hcons := InternalListMapProof.consForward F (jobs.relabel j) (head.relabel j) (tail.relabel j)
   (ys 1) (ys 0) (tagged.relabel j) Fin.elim0 hc' hv hmap (andRight hf')
 have htail := rowApply F (size.relabel j) (tail.relabel j) (ys 0) hi' (andIntro hl' hmap)
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,sucRelabel]
 exact OriginalContextInsertionLengthProof.lengthCons (tagged.relabel j) (ys 1) (ys 0) (size.relabel j) hcons htail

theorem successorCore (F : Program 1) (size jobs tagged : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row F size)))
 (hf : Nonempty (Derivation body Delta (fields F (suc size) jobs tagged))) :
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc size) tagged)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases jobs _
   (OriginalContextInsertionSupportProof.successorLengthNonzero size jobs (andLeft hf))
 intro beta j Theta head tail hinc hc
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [rowRename,fieldsRename,sucRelabel] at hi' hf'
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,sucRelabel]
 exact consCore F (size.relabel j) (jobs.relabel j) head tail (tagged.relabel j) hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthStep
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthStep
