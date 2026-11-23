module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedPositiveUnitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedUnitFromCoverProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape callbackAt)
open NumberedWindowInternalSparseCoverScratchOpenSyntaxProof (optionFromCallback)
open NumberedWindowInternalSparseCoverScratchOpenBranchProof (scratchZero)
open NumberedWindowInternalFactoredCoverTargets (rawCall generatorCall)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)
open NumberedWindowInternalCoverRefinedPositiveUnitProof (exact_OpenRefinedSyntaxUnitFromPositive)
open NumberedWindowInternalCoverCombinedRestrictedPositiveLengthProof (nonzeroScratch)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedSeedPresenceChecks (exact_SeedInGivenVertices)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rejectCover (V N : Program 1) (s : Settings) (q : OTerm α)
    (zero : Nonempty (Derivation body Γ (unary V z q))) :
    Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V N) s) z q)) := by
  let C := selectedCover V N
  let xs := callbackTape s q
  have selected : Nonempty (Derivation body Γ (programGraph (rawCall V) z xs)) := by
    apply compositionValue V (fun _ : Fin 1 => .projection (2 : Fin 3)) z xs ![q] zero
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (2 : Fin 3) xs
  have cb : Nonempty (Derivation body Γ (callbackAt C s z q)) :=
    zeroBranchIntro (rawCall V) (constantZero 3) (generatorCall N selectedGrammarOption) z xs
      selected (constantZeroValue xs)
  exact scratchZero C s q (optionFromCallback C s z q cb)

/-- An actual member in the original scratch at its own seed forces unit
acceptance of the exact selected syntax, independently of its oracle inputs. -/
theorem exact_OpenRefinedUnitFromOwnScratch (V TV N : Program 1) (s : Settings)
    (q vertices : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover (refinedSyntax V TV) N) s)
      vertices q)))
    (member : Nonempty (Derivation body Γ (memberGraph vertices q))) :
    Nonempty (Derivation body Γ (unary (refinedSyntax V TV) (suc z) q)) := by
  let Q := refinedSyntax V TV
  let C := selectedCover Q N
  apply optionGraphCases Q ![q] _
  · intro β j Δ keep zero
    rw [unaryInputsRename] at zero
    simp only [unaryRename,sucRelabel,zRelabel]
    have old := renameInto cover j Δ keep
    rw [unaryRename] at old
    have hit := renameInto member j Δ keep
    rw [graphRename] at hit
    have nil := rejectCover Q N s (q.relabel j) zero
    obtain ⟨eq⟩ := valueUnique (scratchVertices C s) (vertices.relabel j) z ![q.relabel j] old nil
    obtain ⟨notZero⟩ := nonzeroScratch (vertices.relabel j) (q.relabel j) hit
    exact ⟨Derivation.explosion (Derivation.implicationElimination notZero eq)⟩
  · intro β j Δ out keep positive
    rw [unaryInputsRename] at positive
    simp only [unaryRename,sucRelabel,zRelabel]
    exact exact_OpenRefinedSyntaxUnitFromPositive V TV (q.relabel j) out positive

/-- Packed least certifies unit syntax of its actual raw seed. This is
not a statement about the seed's typed window or lexical admission. -/
theorem exact_OpenRefinedUnitFromPackedLeast (V TV N : Program 1) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty q x : OTerm α)
    (least : Nonempty (Derivation body Γ (leastGraph (selectedCover (refinedSyntax V TV) N) X W s ctx ty q x))) :
    Nonempty (Derivation body Γ (unary (refinedSyntax V TV) (suc z) q)) := by
  let C := selectedCover (refinedSyntax V TV) N
  apply programCases (scratchVertices C s) ![q] _
  intro β j Δ vertices keep cover
  rw [unaryInputsRename] at cover
  simp only [unaryRename,sucRelabel,zRelabel]
  have actual := renameInto least j Δ keep
  rw [leastRename] at actual
  obtain ⟨rule⟩ := exact_SeedInGivenVertices C X W s body β Δ (ctx.relabel j) (ty.relabel j)
    (q.relabel j) (x.relabel j) vertices
  obtain ⟨actual⟩ := actual
  obtain ⟨cv⟩ := cover
  exact exact_OpenRefinedUnitFromOwnScratch V TV N s (q.relabel j) vertices ⟨cv⟩
    ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction actual cv)⟩

#print axioms exact_OpenRefinedUnitFromOwnScratch
#print axioms exact_OpenRefinedUnitFromPackedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedUnitFromCoverProof
