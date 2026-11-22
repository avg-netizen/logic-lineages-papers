module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenTargets (ExactOpenPackedLeastPoolOccurrence)
open NumberedWindowInternalSparseRoundsInclusionTargets (MembersIncluded PassIncluded)

def coverRow {α : Type} (C : Program 3) (s : Settings) (seed k vertices : OTerm α) : Formula α :=
  unary (scratchVertices C s) vertices seed ⊓ memberGraph vertices k

def occursInCover {α : Type} (C : Program 3) (s : Settings) (seed k : OTerm α) : Formula α :=
  let lift : α → α ⊕ Fin 1 := Sum.inl
  existsOne (coverRow C s (seed.relabel lift) (k.relabel lift) (.var (.inr 0)))

/-- The filtered members pool and the original cover vertices have different
roles. The witness in the conclusion is an actual output of the original
cover projection on exactly the unchanged seed. -/
def ExactMembersOccurrenceInCover : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings),
    MembersIncluded (edge4 X W) →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (ctx ty seed pool k : OTerm α),
      Nonempty (Derivation body Γ
        ((programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool k).imp
          (occursInCover C s seed k)))

/-- Successful physical least yields the same candidate in the original
cover. The premises are precisely the two internal rules for occurrence
in the computed members pool and containment for a directed pass. -/
def ExactPackedLeastOccurrenceFromPass : Prop :=
  ExactOpenPackedLeastPoolOccurrence → (∀ E, PassIncluded E) →
    ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
      (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed k : OTerm α),
      Nonempty (Derivation body Γ ((leastGraph C X W s ctx ty seed k).imp (occursInCover C s seed k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
