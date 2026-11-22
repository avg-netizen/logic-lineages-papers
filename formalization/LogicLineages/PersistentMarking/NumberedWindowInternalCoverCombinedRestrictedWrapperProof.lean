module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedInductionProof (exact_OpenCoverCombinedRestrictedInductionOwn)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTapeProof (rawValueOnMatchingTape ownSeedOnSameMatchingTape)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem wrapAtActualOwn (C baseW : Program 3) (V : Program 1) (s : Settings) (ctx ty raw vertices : OTerm α)
    (valid : Nonempty (Derivation body Γ (unary V (suc z) raw)))
    (typed : Nonempty (Derivation body Γ (windowAt baseW ctx ty raw)))
    (context : Nonempty (Derivation body Γ (windowAt thinContextPresent ctx ty raw)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices raw)))
    (hit : Nonempty (Derivation body Γ (memberGraph vertices raw))) :
    Nonempty (Derivation body Γ (windowAt (thinMatchingWindow C s baseW V) ctx ty raw)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,raw]
  let F : Program 3 := .composition V (fun _ : Fin 1 => .projection 2)
  let D := conjunction thinContextPresent (thinOwnSeed C s)
  have syntaxRun : Nonempty (Derivation body Γ (programGraph (thinSyntaxWindow baseW V) (suc z) xs)) :=
    conjunctionAccept baseW F xs typed (rawValueOnMatchingTape V ctx ty raw (suc z) valid)
  have own := ownSeedOnSameMatchingTape C s ctx ty raw vertices held hit
  have guard := conjunctionAccept thinContextPresent (thinOwnSeed C s) xs context own
  exact conjunctionAccept (thinSyntaxWindow baseW V) D xs syntaxRun guard

theorem exact_OpenCoverCombinedRestrictedWrapper : ExactOpenCoverCombinedRestrictedWrapper := by
  intro V TV M M0 B T s body α Γ ctx ty raw P valid typed context
  let C : Program 3 := P.cover
  let W : Program 3 := thinMatchingWindow C s P.W P.V
  let goal : Formula α := windowAt W ctx ty raw
  apply programCases (scratchVertices C s) ![raw] goal
  intro β j Δ vertices keep output
  rw [unaryInputsRename] at output
  let q := raw.relabel j
  let c := ctx.relabel j
  let t := ty.relabel j
  have selected := renameInto valid j Δ keep
  simp only [unaryRename,zRelabel,sucRelabel] at selected
  have typed' := renameInto typed j Δ keep
  have context' := renameInto context j Δ keep
  rw [windowRename] at typed' context'
  have hit := exact_OpenCoverCombinedRestrictedInductionOwn V TV M M0 B T s body β Δ
    q vertices c t selected typed' output
  change Nonempty (Derivation body Δ ((windowAt W ctx ty raw).relabel j))
  rw [windowRename]
  exact wrapAtActualOwn C P.W P.V s c t q vertices selected typed' context' output hit

#print axioms wrapAtActualOwn
#print axioms exact_OpenCoverCombinedRestrictedWrapper

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperProof
