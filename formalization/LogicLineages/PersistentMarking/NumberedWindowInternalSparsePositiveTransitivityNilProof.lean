module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySeedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTerminalChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityNilProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveIterationTerminalChecks (exact_OpenTerminalNilLoop)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)
open NumberedWindowInternalSparsePositiveOutputFinishProof (terminalValue)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt finishAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename finishAtRename)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (provide suppliedRename)
open NumberedWindowInternalSparsePositiveTransitivityTransportProof (moveSource)

attribute [local irreducible] programGraph finish

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem useNilScratch (raw : Program 5) (least : Program 3)
    (ctx ty source mid second target state : OTerm α)
    (known : Nonempty (Derivation body Γ (finishAt raw least ctx ty source z mid)))
    (followed : Nonempty (Derivation body Γ (positiveAt raw least ctx ty mid second target)))
    (pair : Nonempty (Derivation body Γ (scratchGraph state z (suc source)))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  have loop := closedApply (exact_OpenTerminalNilLoop body raw least α state z ctx ty (suc source)) pair
  have original := terminalValue raw least state ctx ty (suc source) z z (suc source) loop pair ⟨refl z⟩
  obtain ⟨e⟩ := valueUnique (finish raw least) (suc mid) (suc source)
    (args4 ctx ty (suc source) z) known original
  have lifted := moveSource raw least ctx ty mid source second target ⟨cancelSuc e⟩ followed
  exact provide raw least ctx ty source target second lifted

theorem fromNil (raw : Program 5) (least : Program 3) (ctx ty source mid second target : OTerm α)
    (known : Nonempty (Derivation body Γ (finishAt raw least ctx ty source z mid)))
    (followed : Nonempty (Derivation body Γ (positiveAt raw least ctx ty mid second target))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  apply scratchCases z (suc source) (supplied raw least ctx ty source target)
  intro β j Δ state hJ pair
  rw [suppliedRename]
  simp only [zRelabel,sucRelabel] at pair
  have a := renameInto known j Δ hJ
  rw [finishAtRename,zRelabel] at a
  have b := renameInto followed j Δ hJ
  rw [positiveRename] at b
  exact useNilScratch raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
    (mid.relabel j) (second.relabel j) (target.relabel j) state a b pair

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityNilProof
