module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open VisitListCompletionDefinitions VisitListCompletionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withHead (R : Program 2) (size job frame tailTagged tagged headCount value : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta (Completion R size tailTagged)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged))) :
 Nonempty (Derivation body Delta (Completion R (suc size) tagged)) := by
 apply completionCases R size tailTagged _ ht
 intro beta j Theta tailCount tailRow hinc ht'
 simp only [completionRename,sucRelabel]
 have hh' := renameInto hh j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 simp only [JobFrameSyntax.frameRename,graph2Rename,numeralRename] at hh' hf' hc'
 exact VisitListCompletionConsQueries.withSingleFrame R (size.relabel j) (job.relabel j) (frame.relabel j)
   (tailTagged.relabel j) (tagged.relabel j) (headCount.relabel j) (value.relabel j) tailCount tailRow hh' ht' hf' hc'

theorem actualCons : VisitListCompletionTargets.ActualCons := by
 intro R body alpha Delta size job frame tailTagged tagged hh ht hf hc
 apply JobCompletionSyntax.completionCases R job _ hh
 intro beta j Theta headCount value hinc hh'
 simp only [completionRename,sucRelabel]
 have ht' := renameInto ht j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 simp only [completionRename,graph2Rename,numeralRename] at ht' hf' hc'
 exact withHead R (size.relabel j) (job.relabel j) (frame.relabel j) (tailTagged.relabel j) (tagged.relabel j)
   headCount value hh' ht' hf' hc'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsProof
