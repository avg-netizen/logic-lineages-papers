module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnSupplierProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromRows (raw children deletions produced childRow backward deletionPrefix first second row : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (InternalAdditionLawsProof.add children deletions) produced)))
 (hc : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph children childRow)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backward childRow)))
 (hd : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions deletionPrefix)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backward)))
 (hrow : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row deletionPrefix)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (numeral 0) childRow)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) childRow))) :
 UniformReturnSupplierProof.Supplier body Delta children deletions produced first second row := by
 apply UniformReturnSupplierProof.fromData children deletions produced deletionPrefix backward first second row hl hd hp hrow
 intro beta j Theta old results hi happend
 have ha' := renameInto ha j Theta hi
 have hc' := renameInto hc j Theta hi
 have hr' := renameInto hr j Theta hi
 have hd' := renameInto hd j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have hs' := renameInto hs j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename] at ha' hc' hr' hd' hp' hf' hs'
 exact SixSol20261113.Context.ReverseChildSlotsProof.actual body beta Theta
   (raw.relabel j) (children.relabel j) (deletions.relabel j) (childRow.relabel j) (backward.relabel j) (deletionPrefix.relabel j) (produced.relabel j) old results (first.relabel j) (second.relabel j)
   ha' hc' hr' hd' hp' happend hf' hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnSupplierProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnSupplierProof
