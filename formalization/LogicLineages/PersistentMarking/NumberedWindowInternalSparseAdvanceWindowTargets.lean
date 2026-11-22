module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc hopCertified)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

/-- Recover the original raw and two minimum calls for the supplied certified
hop, both raw endpoint window guards and both occurrences in their respective
source covers at the accepted initial and terminal states. -/
def ExactCertifiedAdvanceCovers : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W root other : Program 3) (syntaxProg : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty current hop target q w r : OTerm α),
    let raw := typedRaw5 root other W syntaxProg
    let least := packedLeastProgram C X W s
    let accepted := selectedGraph raw least (suc target) ctx ty (suc current) hop
    let facts := hopCalls raw least ctx ty current hop target q w r ⊓
      ((windowAt W ctx ty q ⊓ windowAt W ctx ty r) ⊓
        (occursInCover C s q current ⊓ occursInCover C s r target))
    Nonempty (Derivation body Γ ((accepted ⊓ hopCertified hop target q w r).imp facts))

/-- No parsed hop, raw endpoints or seed admission is supplied. The two
decoded class states use the same window as the physical raw and least calls. -/
def ExactSuccessfulAdvanceWindowsFromRetained : Prop :=
  ExactRetainedPredecessor →
    ∀ (C : Program 3) (X : Program 2) (W root other : Program 3) (syntaxProg : Program 1) (s : Settings)
      (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty current hop target : OTerm α),
      let raw := typedRaw5 root other W syntaxProg
      let least := packedLeastProgram C X W s
      Nonempty (Derivation body Γ ((selectedGraph raw least (suc target) ctx ty (suc current) hop).imp
        (windowAt W ctx ty current ⊓ windowAt W ctx ty target)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowTargets
