module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaRootValueProof
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
attribute [local irreducible] OriginalRootObservation.rootObservation InternalPairing.pairing InternalListCodec.consCode

theorem valueAtFields (Q : Program 2) (input domain codomain child arrow parameter childParameter c gamma extended value observed typedData data out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields input domain codomain child arrow)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c extended)))
 (hv : Nonempty (Derivation body Delta (graph2 Q value child childParameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observed codomain value)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData codomain observed)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) data)))
 :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) out input parameter)) := by
 let psi : Formula alpha := graph2 (OriginalRootObservation.rootObservation Q) out input parameter
 change Nonempty (Derivation body Delta psi)
 apply OriginalPackedSourceLambdaChildProof.rawCoordinates input child domain codomain arrow psi hf
 intro beta rho Theta node inner raw hrho houter hnode hinner hbody
 change Nonempty (Derivation body Theta ((graph2 (OriginalRootObservation.rootObservation Q) out input parameter).relabel rho))
 rw [graph2Rename]
 have hf' := renameInto hf rho Theta hrho
 rw [fieldsRename] at hf'
 have hp' := renameInto hp rho Theta hrho
 rw [graph2Rename] at hp'
 have he' := renameInto he rho Theta hrho
 rw [graph2Rename] at he'
 have hcp' := renameInto hcp rho Theta hrho
 rw [graph2Rename] at hcp'
 have hv' := renameInto hv rho Theta hrho
 rw [graph2Rename] at hv'
 have ho' := renameInto ho rho Theta hrho
 rw [graph2Rename] at ho'
 have ht' := renameInto ht rho Theta hrho
 rw [graph2Rename] at ht'
 have hd' := renameInto hd rho Theta hrho
 rw [graph2Rename] at hd'
 have hout' := renameInto hout rho Theta hrho
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hout'
 have ha : Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (arrow.relabel rho) (domain.relabel rho) (codomain.relabel rho))) :=
  andLeft (andRight (andRight hf'))
 exact OriginalRootObservationInternalProof.lambdaLaw Q body beta Theta
  (input.relabel rho) (parameter.relabel rho) (arrow.relabel rho) node (domain.relabel rho) (codomain.relabel rho) inner raw (child.relabel rho)
  (c.relabel rho) (gamma.relabel rho) (extended.relabel rho) (childParameter.relabel rho) (value.relabel rho) (observed.relabel rho) (typedData.relabel rho) (data.relabel rho) (out.relabel rho) houter hnode hinner
  ha hbody hp' he' hcp' hv' ho' ht' hd' hout'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaRootValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaRootValueProof
