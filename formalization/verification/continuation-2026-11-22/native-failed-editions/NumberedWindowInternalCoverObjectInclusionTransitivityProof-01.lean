module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverObjectInclusionTransitivityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverArgumentCellsTransportProof (axisRename)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (pairInclusion)

private theorem applyAxis {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (a b v : OTerm α) (includeAB : Derivation body Γ (axisInclusion a b))
    (memberA : Derivation body Γ (memberGraph a v)) :
    Derivation body Γ (memberGraph b v) := by
  have chosen := Derivation.universalElimination (emb v) includeAB
  have clause : Derivation body Γ ((memberGraph a v).imp (memberGraph b v)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using chosen
  exact Derivation.implicationElimination clause memberA

/-- Compose exact object membership at the unchanged intermediate list and key. -/
theorem composeAxis (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (a b c : OTerm α)
    (ab : Nonempty (Derivation body Γ (axisInclusion a b)))
    (bc : Nonempty (Derivation body Γ (axisInclusion b c))) :
    Nonempty (Derivation body Γ (axisInclusion a c)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := memberGraph (a.relabel j) key
  let Δ := P :: Γ.map (fun q => q.relabel j)
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have ab' := renameInto ab j Δ keep
  have bc' := renameInto bc j Δ keep
  rw [axisRename] at ab' bc'
  obtain ⟨l⟩ := ab'
  obtain ⟨r⟩ := bc'
  have mid := applyAxis (a.relabel j) (b.relabel j) key l
    (Derivation.hypothesis List.mem_cons_self)
  have last := applyAxis (b.relabel j) (c.relabel j) key r mid
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction last)⟩

/-- Compose the original ordered pair of term/argument inclusions separately. -/
theorem composePair (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (aTerms bt ct aa ba ca : OTerm α)
    (ab : Nonempty (Derivation body Γ (pairInclusion aTerms bt aa ba)))
    (bc : Nonempty (Derivation body Γ (pairInclusion bt ct ba ca))) :
    Nonempty (Derivation body Γ (pairInclusion aTerms ct aa ca)) := by
  obtain ⟨l⟩ := ab
  obtain ⟨r⟩ := bc
  obtain ⟨terms⟩ := composeAxis body α Γ aTerms bt ct
    ⟨Derivation.conjunctionLeft l⟩ ⟨Derivation.conjunctionLeft r⟩
  obtain ⟨args⟩ := composeAxis body α Γ aa ba ca
    ⟨Derivation.conjunctionRight l⟩ ⟨Derivation.conjunctionRight r⟩
  exact ⟨Derivation.conjunctionIntroduction terms args⟩

#print axioms composeAxis
#print axioms composePair

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverObjectInclusionTransitivityProof
