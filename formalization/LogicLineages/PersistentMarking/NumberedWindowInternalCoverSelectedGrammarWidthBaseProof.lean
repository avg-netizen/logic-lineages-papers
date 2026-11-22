module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenBaseProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverSelectedGrammarOpenBaseProof (exact_OpenSelectedGrammarBaseSplit)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets
open NumberedWindowInternalCoverSelectedGrammarWidthBindingProof (buildWidth)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem includeFromEquality (old next : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn old next))) :
    Nonempty (Derivation body Γ (axisInclusion old next)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let m := memberGraph (old.relabel j) key
  let Δ := m :: Γ.map (fun p => p.relabel j)
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := renameInto same j Δ keep
  rw [eqnRelabel] at he
  obtain ⟨moved⟩ := headTransport scratchMember (suc z) (old.relabel j) (next.relabel j)
    ![key] he ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction moved)⟩

private theorem equalBase (H K m M old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (small : Nonempty (Derivation body Γ (observed z H K m old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed z H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  obtain ⟨a⟩ := small
  obtain ⟨b⟩ := large
  have ar := Derivation.conjunctionRight a
  have br := Derivation.conjunctionRight b
  obtain ⟨low⟩ := exact_OpenSelectedGrammarBaseSplit body α Γ old oldTerms oldArgs H K m
    ⟨Derivation.conjunctionLeft a⟩ ⟨Derivation.conjunctionLeft ar⟩ ⟨Derivation.conjunctionRight ar⟩
  obtain ⟨high⟩ := exact_OpenSelectedGrammarBaseSplit body α Γ next nextTerms nextArgs H K M
    ⟨Derivation.conjunctionLeft b⟩ ⟨Derivation.conjunctionLeft br⟩ ⟨Derivation.conjunctionRight br⟩
  have sameT := trans (symm (Derivation.conjunctionLeft low)) (Derivation.conjunctionLeft high)
  have sameA := trans (symm (Derivation.conjunctionLeft (Derivation.conjunctionRight low)))
    (Derivation.conjunctionLeft (Derivation.conjunctionRight high))
  obtain ⟨includeT⟩ := includeFromEquality oldTerms nextTerms ⟨sameT⟩
  obtain ⟨includeA⟩ := includeFromEquality oldArgs nextArgs ⟨sameA⟩
  exact ⟨Derivation.conjunctionIntroduction includeT includeA⟩

theorem widthAtZero (H K m M : OTerm α) :
    Nonempty (Derivation body Γ (widthAt z H K m M)) := by
  apply buildWidth z H K m M
  intro β j Δ old oldTerms oldArgs next nextTerms nextArgs keep small large
  simp only [zRelabel] at small large
  exact equalBase (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j)
    old oldTerms oldArgs next nextTerms nextArgs small large

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBaseProof
