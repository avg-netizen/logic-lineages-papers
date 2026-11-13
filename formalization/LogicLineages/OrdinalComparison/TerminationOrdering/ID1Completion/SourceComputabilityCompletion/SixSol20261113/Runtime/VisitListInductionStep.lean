module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionBase
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionAllProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionStep
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open VisitListCompletionDefinitions VisitListCompletionSyntax VisitListInductionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem consCore (R : Program 2) (size jobs head tail tagged : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R size)))
 (hf : Nonempty (Derivation body Delta (fields R (suc size) jobs tagged)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs head tail))) :
 Nonempty (Derivation body Delta (Completion R (suc size) tagged)) := by
 have hl := OriginalContextInsertionSupportProof.successorLengthTail jobs head tail size hc (andLeft hf)
 have hh := VisitListCompletionAllProof.headComplete R size jobs head tail (andRight (andRight hf)) hc
 have ht := VisitListCompletionAllProof.tailComplete R size jobs head tail (andRight (andRight hf)) hc
 let tp : Program 2 := .composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => .projection 1)
 let vp : Program 2 := pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
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
 have hh' := renameInto hh j Theta hinc
 have ht' := renameInto ht j Theta hinc
 simp only [rowRename,fieldsRename,sucRelabel,graph2Rename,OriginalContextInsertionSyntaxProof.lengthRename,
   JobCompletionSyntax.completionRename,allRename] at hi' hf' hc' hl' hh' ht'
 have hmap := unaryRecover OriginalHereditaryVisitScheduler.tagVisits (.projection 1)
   (ys 0) (tail.relabel j) xx (hq 0) (projectionValue 1 xx)
 have hv := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
   (ys 1) z (head.relabel j) xx (hq 1) (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx) (projectionValue 0 xx)
 have hcons := OriginalHereditaryAgendaPotentialTaggedHelpersProof.tagCons
   (jobs.relabel j) (head.relabel j) (tail.relabel j) (tagged.relabel j) (ys 1) (ys 0) hc' hv hmap (andLeft (andRight hf'))
 have htail := rowApply R (size.relabel j) (tail.relabel j) (ys 0) hi' (andIntro hl' (andIntro hmap ht'))
 simp only [completionRename,sucRelabel]
 exact VisitListCompletionConsProof.actualCons R body beta Theta (size.relabel j) (head.relabel j)
   (ys 1) (ys 0) (tagged.relabel j) hh' htail hv hcons

theorem successorCore (R : Program 2) (size jobs tagged : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R size)))
 (hf : Nonempty (Derivation body Delta (fields R (suc size) jobs tagged))) :
 Nonempty (Derivation body Delta (Completion R (suc size) tagged)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases jobs _
   (OriginalContextInsertionSupportProof.successorLengthNonzero size jobs (andLeft hf))
 intro beta j Theta head tail hinc hc
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [rowRename,fieldsRename,sucRelabel] at hi' hf'
 simp only [completionRename,sucRelabel]
 exact consCore R (size.relabel j) (jobs.relabel j) head tail (tagged.relabel j) hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionStep
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionStep
