module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem advanceZero (index old out q : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing old q z)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out q (suc z)))) :
    Nonempty (Derivation body Delta (graph2 splitStep out index old)) := by
  let xs : Fin 2 → OTerm alpha := ![index,old]
  have hl := unaryValue InternalUnpair.left (.projection 1) q old xs
    (pairLeft old q z hi) (projectionValue 1 xs)
  have hr := unaryValue InternalUnpair.right (.projection 1) z old xs
    (pairRight old q z hi) (projectionValue 1 xs)
  have hv := binaryValue InternalPairing.pairing (leftOf (.projection 1))
    (OriginalRawSyntaxTransport.constant 2 1) out q (suc z) xs ho hl (constantValue 1 xs)
  exact zeroBranchIntro (rightOf (.projection 1))
    (pairOf (leftOf (.projection 1)) (OriginalRawSyntaxTransport.constant 2 1))
    (pairOf (OriginalRawSyntaxTransport.succOf (leftOf (.projection 1)))
      (OriginalRawSyntaxTransport.constant 2 0)) out xs hr hv

theorem advanceOne (index old out q : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing old q (suc z))))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc q) z))) :
    Nonempty (Derivation body Delta (graph2 splitStep out index old)) := by
  let xs : Fin 2 → OTerm alpha := ![index,old]
  have hl := unaryValue InternalUnpair.left (.projection 1) q old xs
    (pairLeft old q (suc z) hi) (projectionValue 1 xs)
  have hr := unaryValue InternalUnpair.right (.projection 1) (suc z) old xs
    (pairRight old q (suc z) hi) (projectionValue 1 xs)
  have hsucc := unaryValue .succ (leftOf (.projection 1)) (suc q) q xs
    (successorValue (Fin.cons q Fin.elim0)) hl
  have hv := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.succOf (leftOf (.projection 1)))
    (OriginalRawSyntaxTransport.constant 2 0) out (suc q) z xs ho hsucc (constantValue 0 xs)
  exact successorBranchIntro (rightOf (.projection 1))
    (pairOf (leftOf (.projection 1)) (OriginalRawSyntaxTransport.constant 2 1))
    (pairOf (OriginalRawSyntaxTransport.succOf (leftOf (.projection 1)))
      (OriginalRawSyntaxTransport.constant 2 0)) out z xs hr hv

theorem splitZero : Nonempty (Derivation body Delta (graph1 split z z)) :=
  recursionZeroValue (OriginalRawSyntaxTransport.constant 0 0) splitStep z Fin.elim0 (constantValue 0 Fin.elim0)

theorem splitSuccessor (index old out : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph1 split old index)))
    (hs : Nonempty (Derivation body Delta (graph2 splitStep out index old))) :
    Nonempty (Derivation body Delta (graph1 split out (suc index))) := by
  unfold graph1 split programGraph at hi ⊢
  unfold graph2 programGraph at hs
  change Nonempty (Derivation body Delta (InternalRecursionGraph.recursion
    (OrdinaryArithmetic.graphFormula (OriginalRawSyntaxTransport.constant 0 0))
    (OrdinaryArithmetic.graphFormula splitStep) old index Fin.elim0)) at hi
  change Nonempty (Derivation body Delta (InternalRecursionGraph.recursion
    (OrdinaryArithmetic.graphFormula (OriginalRawSyntaxTransport.constant 0 0))
    (OrdinaryArithmetic.graphFormula splitStep) out (suc index) Fin.elim0))
  exact InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction Delta
    (OrdinaryArithmetic.graphFormula (OriginalRawSyntaxTransport.constant 0 0))
    (OrdinaryArithmetic.graphFormula splitStep) out index old Fin.elim0 hi hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.StepProof
