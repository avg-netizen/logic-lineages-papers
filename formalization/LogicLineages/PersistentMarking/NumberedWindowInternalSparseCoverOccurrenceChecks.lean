module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph poolOccurrence)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (binder occurrenceUnfold)
open NumberedWindowInternalSparseRoundsInclusionTargets (MembersIncluded)
open NumberedWindowInternalSparseRoundsInclusionChecks (exact_RoundsInclusionFromPass)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverRename)
open NumberedWindowInternalSparseCoverOccurrenceTargets

theorem exact_MembersOccurrenceInCover : ExactMembersOccurrenceInCover :=
  NumberedWindowInternalSparseCoverOccurrenceMembersProof.membersOccurrence

private theorem forgetContextAndPool (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (inc : MembersIncluded (edge4 X W)) {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx ty seed k : OTerm α)
    (supplied : Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed k))) :
    Nonempty (Derivation body Γ (occursInCover C s seed k)) := by
  rw [occurrenceUnfold] at supplied
  obtain ⟨both⟩ := supplied
  let a := binder C X W s ctx ty seed k
  let Δ := existsOne a :: Γ.map weaken
  let Θ := a :: Δ.map weaken
  let lift (t : OTerm α) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) :=
    (t.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  let pool : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  have atPool : Derivation body Θ a := Derivation.hypothesis List.mem_cons_self
  obtain ⟨step⟩ := exact_MembersOccurrenceInCover C X W s inc body _ Θ
    (lift ctx) (lift ty) (lift seed) pool (lift k)
  have endResult : Derivation body Θ (weaken (weaken (occursInCover C s seed k))) := by
    change Derivation body Θ (((occursInCover C s seed k).relabel
      (Sum.inl : α → α ⊕ Fin 1)).relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1))
    rw [coverRename,coverRename]
    exact Derivation.implicationElimination step (Derivation.conjunctionRight atPool)
  have withPayload : Derivation body Δ (weaken (occursInCover C s seed k)) :=
    Derivation.existentialElimination (Derivation.hypothesis List.mem_cons_self) endResult
  exact ⟨Derivation.existentialElimination both withPayload⟩

theorem exact_PackedLeastOccurrenceFromPass : ExactPackedLeastOccurrenceFromPass := by
  intro physical allPasses C X W s body α Γ ctx ty seed k
  have inc := (exact_RoundsInclusionFromPass (edge4 X W)
    (allPasses (constantZero 4)) (allPasses (edge4 X W))).2
  let P := leastGraph C X W s ctx ty seed k
  obtain ⟨recover⟩ := physical body α (P :: Γ) C X W s ctx ty seed k
  have h : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := forgetContextAndPool C X W s inc ctx ty seed k
    ⟨Derivation.implicationElimination recover h⟩
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_MembersOccurrenceInCover
#print axioms exact_PackedLeastOccurrenceFromPass
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceChecks
