module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePackedLeast (contextOption)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinContextPresent)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftActualContextParser (out ctx ty raw : OTerm α)
    (parsed : Nonempty (Derivation body Γ (unary parser out ctx))) :
    Nonempty (Derivation body Γ (programGraph contextOption out ![ctx,ty,raw])) := by
  apply compositionValue parser (fun _ : Fin 1 => .projection 0) out ![ctx,ty,raw] ![ctx] parsed
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![ctx,ty,raw]

theorem exact_OpenCoverThinMatchingContextTransport : ExactOpenCoverThinMatchingContextTransport := by
  intro body α Γ ctx oldTy oldRaw newTy newRaw present
  let goal : Formula α := windowAt thinContextPresent ctx newTy newRaw
  apply optionGraphCases parser (![ctx] : Fin 1 → OTerm α) goal
  · intro β j Δ keep zero
    rw [unaryInputsRename] at zero
    have before := renameInto present j Δ keep
    rw [windowRename] at before
    let xs := ![ctx.relabel j,oldTy.relabel j,oldRaw.relabel j]
    have absent := liftActualContextParser z (ctx.relabel j) (oldTy.relabel j) (oldRaw.relabel j) zero
    have rejected := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs absent before
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z xs rejected (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ payload keep parsed
    rw [unaryInputsRename] at parsed
    change Nonempty (Derivation body Δ ((windowAt thinContextPresent ctx newTy newRaw).relabel j))
    rw [windowRename]
    let xs := ![ctx.relabel j,newTy.relabel j,newRaw.relabel j]
    have found := liftActualContextParser (suc payload) (ctx.relabel j) (newTy.relabel j) (newRaw.relabel j) parsed
    exact successorBranchIntro contextOption (constantZero 3) (constantOne 3) (suc z) payload xs
      found (oneConstantValue xs)

#print axioms exact_OpenCoverThinMatchingContextTransport

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof
