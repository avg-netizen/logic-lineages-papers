module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTerminalChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFuelCompareProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalUnpairReverseSyntaxProof (weakOrderCases)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (iterateState)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph scratchGraph)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs moveLoop moveFuel)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparsePositiveIterationTerminalChecks (exact_OpenTerminalExtraFuel)

attribute [local irreducible] programGraph iterateState

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem compareAlongGap (raw : Program 5) (least : Program 3)
    (left right pred ctx ty next tail current extra : OTerm α)
    (longer : Nonempty (Derivation body Γ (loopGraph raw least left pred ctx ty next tail)))
    (shorter : Nonempty (Derivation body Γ (loopGraph raw least right tail ctx ty next tail)))
    (done : Nonempty (Derivation body Γ (scratchGraph right z current)))
    (additive : Nonempty (Derivation body Γ (eqn (add tail extra) pred))) :
    Nonempty (Derivation body Γ (eqn left right)) := by
  obtain ⟨l⟩ := shorter
  obtain ⟨s⟩ := done
  have h := closedApply (exact_OpenTerminalExtraFuel body raw least α right tail extra ctx ty next tail current)
    ⟨Derivation.conjunctionIntroduction l s⟩
  have extended := moveFuel raw least right (add tail extra) pred ctx ty next tail additive h
  exact valueUnique (iterateState raw least) left right (loopArgs pred ctx ty next tail) longer extended

theorem compareFuel (raw : Program 5) (least : Program 3)
    (left right pred ctx ty next tail current : OTerm α)
    (longer : Nonempty (Derivation body Γ (loopGraph raw least left pred ctx ty next tail)))
    (shorter : Nonempty (Derivation body Γ (loopGraph raw least right tail ctx ty next tail)))
    (done : Nonempty (Derivation body Γ (scratchGraph right z current)))
    (bound : Nonempty (Derivation body Γ (ltF tail (suc pred)))) :
    Nonempty (Derivation body Γ (eqn left right)) := by
  apply weakOrderCases Γ tail pred (eqn left right) bound
  intro β j Δ extra hJ eq
  rw [eqnRelabel]
  have l := moveLoop j Δ hJ raw least left pred ctx ty next tail longer
  have r := moveLoop j Δ hJ raw least right tail ctx ty next tail shorter
  have d := renameInto done j Δ hJ
  rw [scratchRename,zRelabel] at d
  exact compareAlongGap raw least (left.relabel j) (right.relabel j) (pred.relabel j)
    (ctx.relabel j) (ty.relabel j) (next.relabel j) (tail.relabel j) (current.relabel j) extra l r d eq

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFuelCompareProof
