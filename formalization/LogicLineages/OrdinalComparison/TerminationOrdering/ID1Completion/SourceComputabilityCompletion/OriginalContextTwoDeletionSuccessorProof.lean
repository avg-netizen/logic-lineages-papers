module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorValuesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalListCodecSupportProof InternalSourceInversionSupportProof
open InternalBetaTotalityProof (addHyp)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof
open OriginalContextTwoDeletionInductionSyntaxProof hiding rowInstantiate rowSuccessor
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/- Actual length and in-range cutoff force a nonempty original context. -/
open OriginalContextTwoDeletionQueryProof OriginalContextTwoDeletionCoreProof
open OriginalTypedDecoderTransportLogicalProof (iffForward)
theorem successorAt0 (gamma count head tail i j a b upper lower left right : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) (suc j) a b upper lower left right)))
    : Nonempty (Derivation body Delta (result (suc i) (suc j) a b upper lower left right)) := by
  apply consDeletionCases gamma head tail upper (suc j) _ hc (andLeft (andRight (andRight (andRight (andRight (andRight hf))))))
  intro beta rho Theta ut hrho hc0 hd0
  simp only [resultRename,sucRelabel]
  have hrow' := renameInto hrow rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [rowRename] at hrow'
  rw [consGraphRename] at hc'
  simp only [fieldsRename,sucRelabel] at hf'
  exact successorAt1 (gamma.relabel rho) (count.relabel rho) (head.relabel rho) (tail.relabel rho) (i.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) ut hrow' hc' hf' hc0 hd0


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorProof
