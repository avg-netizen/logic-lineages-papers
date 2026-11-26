module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTailProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaChildProof
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
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalTypedArgumentObservationsAccumulatorQueryProof (binaryCases)

theorem lookupFromObservation (Q : Program 2) (count input parameter c gamma cutoff row value : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)))
 (hv : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff row)) := by
 apply binaryCases InternalRawListRecursion.lookup cutoff row _
 intro beta rho Theta actual hrho ha
 rw [graph2Rename]
 have hp' := renameInto hp rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 have hb' := renameInto hb rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 rw [graph2Rename] at hp' hr'
 rw [lengthRename] at hl'
 simp only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at hb'
 rw [graph3Rename] at hv'
 have hh := OriginalHereditaryDeletionRowsSquareSupportProof.rowExpose Q (count.relabel rho) (input.relabel rho) (parameter.relabel rho) (c.relabel rho) (gamma.relabel rho) (cutoff.relabel rho) (row.relabel rho) actual hp' hl' hb' hr' ha
 have he := valueUnique (OriginalHereditaryDeletionRows.observation Q) actual (value.relabel rho) ![cutoff.relabel rho,input.relabel rho,parameter.relabel rho] hh.1 hv'
 exact outputTransport InternalRawListRecursion.lookup actual (value.relabel rho) ![cutoff.relabel rho,row.relabel rho] he ha

theorem childTailValues (Q : Program 2) (count child otherChild childParameter c extended cutoff childRow otherChildRow tail otherTail value otherValue : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c extended)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) extended)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below (suc cutoff) (suc count))))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) childRow child childParameter)))
 (hr2 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) otherChildRow otherChild childParameter)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop tail (numeral 1) childRow)))
 (hd2 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop otherTail (numeral 1) otherChildRow)))
 (he : Nonempty (Derivation body Delta (equal tail otherTail)))
 (hv : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value (suc cutoff) child childParameter)))
 (hv2 : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) otherValue (suc cutoff) otherChild childParameter))) :
 Nonempty (Derivation body Delta (equal value otherValue)) := by
 have hlookup := lookupFromObservation Q (suc count) child childParameter c extended (suc cutoff) childRow value hp hl hb hr hv
 have hlookup2 := lookupFromObservation Q (suc count) otherChild childParameter c extended (suc cutoff) otherChildRow otherValue hp hl hb hr2 hv2
 have hrow := OriginalHereditaryDeletionRowsSquareSupportProof.rowExpose Q (suc count) child childParameter c extended (suc cutoff) childRow value hp hl hb hr hlookup
 have hrow2 := OriginalHereditaryDeletionRowsSquareSupportProof.rowExpose Q (suc count) otherChild childParameter c extended (suc cutoff) otherChildRow otherValue hp hl hb hr2 hlookup2
 exact OriginalHereditaryDeletionRowsLambdaTailProof.equalTailValues childRow otherChildRow tail otherTail count cutoff value otherValue hrow.2 hrow2.2 hd hd2 he hlookup hlookup2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaChildProof
