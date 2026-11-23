module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedContextFromLeastProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeast (contextOption minimumAtMembers)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinContextPresent)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An actual packed least forces success of its literal context parser.
This is only the context component of the thin window, not term typing. -/
theorem exact_OpenCoverContextFromPackedLeast (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty raw minimum : OTerm α)
    (held : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty raw minimum))) :
    Nonempty (Derivation body Γ (windowAt thinContextPresent ctx ty raw)) := by
  apply optionGraphCases contextOption (![ctx,ty,raw] : Fin 3 → OTerm α) _
  · intro β j Δ keep missing
    rw [tripleInputsRename] at missing
    rw [windowRename]
    have actual := renameInto held j Δ keep
    rw [leastRename] at actual
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,raw.relabel j]
    have lost := zeroBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)
      (suc (minimum.relabel j)) xs missing actual
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc (minimum.relabel j)) z
      xs lost (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ payload keep present
    rw [tripleInputsRename] at present
    rw [windowRename]
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,raw.relabel j]
    exact successorBranchIntro contextOption (constantZero 3) (constantOne 3) (suc z) payload xs
      present (oneConstantValue xs)

#print axioms exact_OpenCoverContextFromPackedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedContextFromLeastProof
