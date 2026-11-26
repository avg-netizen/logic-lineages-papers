module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (consValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets (PositiveLengthK)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem lengthStep (head fuel : OTerm α) :
    Nonempty (Derivation body Γ (programGraph
      (.composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2))) (suc fuel) ![head,fuel])) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection (1 : Fin 2))
    (suc fuel) ![head,fuel] ![fuel] (successorValue ![fuel])
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![head,fuel]

theorem positiveLengthOnCons (vertices head tail : OTerm α) (goal : Formula α)
    (actual : Nonempty (Derivation body Γ (consGraph vertices head tail)))
    (k : PositiveLengthK body Γ vertices goal) : Nonempty (Derivation body Γ goal) := by
  apply programCases poolLength ![tail] goal
  intro β j Δ fuel keep counted
  rw [unaryInputsRename] at counted
  have cell := renameInto actual j Δ keep
  rw [consGraphRename] at cell
  have result : Nonempty (Derivation body Δ (unary poolLength (suc fuel) (vertices.relabel j))) :=
    consValue (constantZero 0) (.composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2)))
      (vertices.relabel j) (head.relabel j) (tail.relabel j) fuel (suc fuel) Fin.elim0 cell counted
      (lengthStep (head.relabel j) fuel)
  exact k β j Δ fuel keep result

#print axioms positiveLengthOnCons
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthConsProof
