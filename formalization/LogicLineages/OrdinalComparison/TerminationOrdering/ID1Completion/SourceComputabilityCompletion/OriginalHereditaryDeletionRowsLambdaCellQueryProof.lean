module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellQueryProof
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
theorem cell (Q : Program 2) (input other domain codomain child otherChild parameter childParameter c gamma extended count childRow otherChildRow tail otherTail cutoff out otherOut : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input domain codomain child parameter childParameter)))
 (hf2 : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields other domain codomain otherChild parameter childParameter)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input domain codomain child)))
 (hc2 : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor other domain codomain otherChild)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hext : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c extended)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) childRow child childParameter)))
 (hr2 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) otherChildRow otherChild childParameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop tail (numeral 1) childRow)))
 (ht2 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop otherTail (numeral 1) otherChildRow)))
 (heq : Nonempty (Derivation body Delta (equal tail otherTail)))
 (hbound : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hobs : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalRootObservation.rootObservation Q)) out cutoff input parameter)))
 (hobs2 : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalRootObservation.rootObservation Q)) otherOut cutoff other parameter)))
 :
 Nonempty (Derivation body Delta (equal out otherOut)) := by
 apply OriginalHereditaryDeletionRowsLambdaQueryProof.coordinateCases Q cutoff gamma c domain input other child otherChild parameter _
 intro beta rho Theta erasedType deleted deletedParam childDeleted childDeletedParam inputE otherE childE otherChildE value otherValue hrho hlookup hdelete hdp hcd hcdp hie hoe hce hoce hq hq2
 rw [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename]
 have hf' := renameInto hf rho Theta hrho
 simp only [lambdaFieldsRename] at hf'
 have hf2' := renameInto hf2 rho Theta hrho
 simp only [lambdaFieldsRename] at hf2'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph3Rename] at hc'
 have hc2' := renameInto hc2 rho Theta hrho
 simp only [graph3Rename] at hc2'
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename] at hp'
 have hlen' := renameInto hlen rho Theta hrho
 simp only [OriginalContextInsertionSyntaxProof.lengthRename] at hlen'
 have hext' := renameInto hext rho Theta hrho
 simp only [graph2Rename] at hext'
 have hcp' := renameInto hcp rho Theta hrho
 simp only [graph2Rename] at hcp'
 have hr' := renameInto hr rho Theta hrho
 simp only [graph2Rename] at hr'
 have hr2' := renameInto hr2 rho Theta hrho
 simp only [graph2Rename] at hr2'
 have ht' := renameInto ht rho Theta hrho
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht'
 have ht2' := renameInto ht2 rho Theta hrho
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht2'
 have heq' := renameInto heq rho Theta hrho
 simp only [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename] at heq'
 have hbound' := renameInto hbound rho Theta hrho
 simp only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at hbound'
 have hobs' := renameInto hobs rho Theta hrho
 simp only [graph3Rename] at hobs'
 have hobs2' := renameInto hobs2 rho Theta hrho
 simp only [graph3Rename] at hobs2'
 exact OriginalHereditaryDeletionRowsLambdaCellProof.cellAtCoordinates Q (input.relabel rho) (other.relabel rho) (domain.relabel rho) (codomain.relabel rho) (child.relabel rho) (otherChild.relabel rho) (parameter.relabel rho) (childParameter.relabel rho) (c.relabel rho) (gamma.relabel rho) (extended.relabel rho) (count.relabel rho) (childRow.relabel rho) (otherChildRow.relabel rho) (tail.relabel rho) (otherTail.relabel rho) (cutoff.relabel rho) erasedType deleted deletedParam childDeleted childDeletedParam inputE otherE childE otherChildE value otherValue (out.relabel rho) (otherOut.relabel rho)
  hf' hf2' hc' hc2' hp' hlen' hext' hcp' hr' hr2' ht' ht2' heq' hbound' hlookup hdelete hdp hcd hcdp hie hoe hce hoce hq hq2 hobs' hobs2'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellQueryProof
