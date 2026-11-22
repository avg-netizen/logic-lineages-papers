module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenBranchesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePackedLeast (contextOption)
open NumberedWindowInternalSparsePackedLeastOpen
open NumberedWindowInternalSparsePackedLeastOpenTargets
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename occurrenceRename)
open NumberedWindowInternalSparsePackedLeastOpenBranchesProof (reject present)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem recover (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α)
    (accepted : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed selected))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α)
    (poolOccurrence C X W s ctx ty seed selected)
  · intro β j Δ keep missing
    rw [tripleInputsRename] at missing
    rw [occurrenceRename]
    have h := renameInto accepted j Δ keep
    rw [leastRename] at h
    exact reject C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
      (selected.relabel j) missing h
  · intro β j Δ payload keep known
    rw [tripleInputsRename] at known
    rw [occurrenceRename]
    have h := renameInto accepted j Δ keep
    rw [leastRename] at h
    exact present C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
      (selected.relabel j) payload known h

theorem exact_OpenPackedLeastPoolOccurrence : ExactOpenPackedLeastPoolOccurrence := by
  intro body α Γ C X W s ctx ty seed selected
  obtain ⟨d⟩ := recover (body := body)
    (Γ := leastGraph C X W s ctx ty seed selected :: Γ)
    C X W s ctx ty seed selected ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenPackedLeastPoolOccurrence
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
