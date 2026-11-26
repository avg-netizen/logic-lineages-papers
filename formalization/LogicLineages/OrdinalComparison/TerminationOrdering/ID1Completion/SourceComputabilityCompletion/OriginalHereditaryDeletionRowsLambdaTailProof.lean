module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTailProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalLambdaTraversalInternalFieldsSyntaxProof (lambdaFieldsRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSyntaxProof (suc sucRelabel z)
open InternalRawListRecursionSupportProof
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalTypedDecoderTransportLogicalProof (iffForward)

theorem tailLookup (row tail count cutoff value : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) row)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop tail (numeral 1) row)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (suc cutoff) row))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff tail)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases row _ (OriginalContextInsertionSupportProof.successorLengthNonzero count row hl)
 intro beta rho Theta head actualTail hrho hc
 rw [graph2Rename]
 have hd' := renameInto hd rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph2Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hd' hv'
 have hone := OriginalAllPositionContextDeleteBaseProof.dropOne (row.relabel rho) head actualTail hc
 have heq := valueUnique InternalRawListRecursion.drop actualTail (tail.relabel rho) ![numeral 1,row.relabel rho] hone hd'
 have hactual := iffForward (OriginalAllPositionContextDeleteDropProof.lookupConsIff (row.relabel rho) head actualTail (cutoff.relabel rho) (value.relabel rho) hc) hv'
 exact OriginalContextTwoDeletionCoreProof.secondInput InternalRawListRecursion.lookup (value.relabel rho) (cutoff.relabel rho) actualTail (tail.relabel rho) heq hactual

theorem equalTailValues (row otherRow tail otherTail count cutoff value otherValue : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) row)))
 (hl2 : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) otherRow)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop tail (numeral 1) row)))
 (hd2 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop otherTail (numeral 1) otherRow)))
 (he : Nonempty (Derivation body Delta (equal tail otherTail)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (suc cutoff) row)))
 (hv2 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup otherValue (suc cutoff) otherRow))) :
 Nonempty (Derivation body Delta (equal value otherValue)) := by
 have h1 := tailLookup row tail count cutoff value hl hd hv
 have h2 := tailLookup otherRow otherTail count cutoff otherValue hl2 hd2 hv2
 rw [equalEqn] at he
 have h1' := OriginalContextTwoDeletionCoreProof.secondInput InternalRawListRecursion.lookup value cutoff tail otherTail he h1
 simpa only [equalEqn] using valueUnique InternalRawListRecursion.lookup value otherValue ![cutoff,otherTail] h1' h2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTailProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTailProof
