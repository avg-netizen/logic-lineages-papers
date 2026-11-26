module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowBasePeelProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowBaseReportsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverRestrictedListWindowBasePeelProof
  (peelOrdinarySelectedBase peelNumberedSelectedBase actualGuardReport)
open NumberedWindowInternalCoverRestrictedListWindowSlotProof (actualRestrictedArgument unliftListGuard)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverRestrictedListWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualRestrictedOrdinaryBase (s : Settings) (G : Program 1) (B : Program 2) (T : Program 1)
    (ctx h a result : OTerm α)
    (seen : Nonempty (Derivation body Γ (programGraph
      (precedingBase s (lambdaLexicalBase s (restrictedListBase G B) T))
      (suc result) ![ctx,ordinaryKey h a]))) :
    Nonempty (Derivation body Γ (unary (argumentReject G) z a)) := by
  let raw := ordinaryKey h a
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let next := ID1Completion.InternalAcceptance.branch (onRaw (header 5 5)) B
    (keepWhenListAllowed (numberedListAllowed G) B)
  have actual := peelOrdinarySelectedBase s (restrictedListBase G B) T ctx h a result seen
  have shape := exact_OpenCoverHeadShape false body α Γ h [a] rfl
  have check := liftRawReport (header 4 2) ctx raw (suc z) shape.accepted
  have allowed := successorBranchElim (onRaw (header 4 2)) next (keepWhenListAllowed (ordinaryListAllowed G) B)
    (suc result) z xs check actual
  have got := actualGuardReport (onRaw (ordinaryListAllowed G)) B result xs allowed
  have tag : Nonempty (Derivation body Γ (unary (literal 1 4) (numeral 4) raw)) := literalGraph 4 ![raw]
  have rows := (packedNode (literal 1 4) (numeral 4) [h,a] tag).2
  exact actualRestrictedArgument G 1 raw a rows.2.1 (unliftListGuard (ordinaryListAllowed G) ctx raw got)

theorem actualRestrictedNumberedBase (s : Settings) (G : Program 1) (B : Program 2) (T : Program 1)
    (ctx h ty k l r result : OTerm α)
    (seen : Nonempty (Derivation body Γ (programGraph
      (precedingBase s (lambdaLexicalBase s (restrictedListBase G B) T))
      (suc result) ![ctx,numberedTerm h ty k l r]))) :
    Nonempty (Derivation body Γ (unary (argumentReject G) z l)) ∧
    Nonempty (Derivation body Γ (unary (argumentReject G) z r)) := by
  let raw := numberedTerm h ty k l r
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let next := ID1Completion.InternalAcceptance.branch (onRaw (header 5 5)) B
    (keepWhenListAllowed (numberedListAllowed G) B)
  have actual := peelNumberedSelectedBase s (restrictedListBase G B) T ctx h ty k l r result seen
  have shape := exact_OpenCoverHeadShape true body α Γ h [ty,k,l,r] rfl
  have check4 := liftRawReport (header 4 2) ctx raw z (shape.notOrdinary rfl)
  have check5 := liftRawReport (header 5 5) ctx raw (suc z) shape.accepted
  have taken := zeroBranchElim (onRaw (header 4 2)) next (keepWhenListAllowed (ordinaryListAllowed G) B)
    (suc result) xs check4 actual
  have allowed := successorBranchElim (onRaw (header 5 5)) B (keepWhenListAllowed (numberedListAllowed G) B)
    (suc result) z xs check5 taken
  have got := actualGuardReport (onRaw (numberedListAllowed G)) B result xs allowed
  obtain ⟨bits⟩ := conjunctionRecover (listSlotAllowed G 3) (listSlotAllowed G 4) ![raw]
    (unliftListGuard (numberedListAllowed G) ctx raw got)
  have tag : Nonempty (Derivation body Γ (unary (literal 1 5) (numeral 5) raw)) := literalGraph 5 ![raw]
  have rows := (packedNode (literal 1 5) (numeral 5) [h,ty,k,l,r] tag).2
  exact ⟨actualRestrictedArgument G 3 raw l rows.2.2.2.1 ⟨Derivation.conjunctionLeft bits⟩,
    actualRestrictedArgument G 4 raw r rows.2.2.2.2.1 ⟨Derivation.conjunctionRight bits⟩⟩

#print axioms actualRestrictedOrdinaryBase
#print axioms actualRestrictedNumberedBase

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowBaseReportsProof
