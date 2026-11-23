module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedParsedScratchDomainProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (contextOption)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparsePackedDomainChecks (exact_PackedDomain)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem leastAtActualContext (C W : Program 3) (X : Program 2) (s : Settings) (ctx ty raw vertices : OTerm α)
    (context : Nonempty (Derivation body Γ (windowAt thinContextPresent ctx ty raw)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices raw)))
    (hit : Nonempty (Derivation body Γ (memberGraph vertices raw))) :
    Nonempty (Derivation body Γ (hasLeast C X W s ctx ty raw)) := by
  apply optionGraphCases contextOption (![ctx,ty,raw] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [tripleInputsRename] at zero
    have good := renameInto context j Δ keep
    rw [windowRename] at good
    let xs := ![ctx.relabel j,ty.relabel j,raw.relabel j]
    have dead := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs zero good
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z xs dead (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename] at parsed
    rw [hasRename]
    have cover := renameInto held j Δ keep
    rw [unaryRename] at cover
    have member := renameInto hit j Δ keep
    rw [graphRename] at member
    obtain ⟨theoremAtTape⟩ := exact_PackedDomain C X W s body β Δ (ctx.relabel j) (ty.relabel j)
      (raw.relabel j) payload (vertices.relabel j)
    obtain ⟨c⟩ := cover
    obtain ⟨m⟩ := member
    obtain ⟨p⟩ := parsed
    have both := Derivation.implicationElimination theoremAtTape (Derivation.conjunctionIntroduction p c)
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight both) m⟩


#print axioms leastAtActualContext
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedParsedScratchDomainProof
