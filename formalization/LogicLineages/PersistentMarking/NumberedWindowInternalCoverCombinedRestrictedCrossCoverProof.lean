module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratchOpenBranchProof (scratchSuccessor)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverIntro)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTapeProof (memberOfOwnSeedOnSameMatchingTape)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
  (thinSyntaxWindow thinMatchingWindow thinContextPresent thinOwnSeed)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets

private theorem readOwnSeed {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C baseW : Program 3) (V : Program 1) (s : Settings) (ctx ty seed : OTerm α)
    (w : Nonempty (Derivation body Γ (windowAt (thinMatchingWindow C s baseW V) ctx ty seed))) :
    Nonempty (Derivation body Γ (windowAt (thinOwnSeed C s) ctx ty seed)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  let extra := conjunction thinContextPresent (thinOwnSeed C s)
  obtain ⟨both⟩ := conjunctionRecover (thinSyntaxWindow baseW V) extra xs w
  obtain ⟨rest⟩ := conjunctionRecover thinContextPresent (thinOwnSeed C s) xs
    ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.conjunctionRight rest⟩

theorem exact_OpenCoverThinCrossCover : ExactOpenCoverThinCrossCover := by
  intro C baseW V s body α Γ ctx ty a b vertices W wa wb ca cb
  have sa := scratchSuccessor C s vertices a ca
  have sb := scratchSuccessor C s vertices b cb
  have ownA := readOwnSeed C baseW V s ctx ty a wa
  have ownB := readOwnSeed C baseW V s ctx ty b wb
  have ma := memberOfOwnSeedOnSameMatchingTape C s ctx ty a vertices sa ownA
  have mb := memberOfOwnSeedOnSameMatchingTape C s ctx ty b vertices sb ownB
  exact ⟨ca,cb,sa,sb,ma,mb,coverIntro C s a b vertices sa mb,coverIntro C s b a vertices sb ma⟩

#print axioms exact_OpenCoverThinCrossCover
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverProof
