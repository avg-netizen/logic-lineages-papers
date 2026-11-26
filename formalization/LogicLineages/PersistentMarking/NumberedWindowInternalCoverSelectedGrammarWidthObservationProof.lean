module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction actualFiniteExistentialElimination)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalUnpair (left right)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalCoverSelectedSuccessorTargets (termProjection argsProjection)
open NumberedWindowInternalCoverSelectedGrammarTargets
open NumberedWindowInternalCoverSelectedGrammarWidthTargets
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observationWitness observationRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem introduce (d H K M state terms args : OTerm α)
    (row : Nonempty (Derivation body Γ (observed d H K M state terms args))) :
    Nonempty (Derivation body Γ (existingObservation d H K M)) := by
  let w : Fin 3 → OTerm α := ![state,terms,args]
  apply actualFiniteExistentialIntroduction body α 3 Γ (observationMatrix d H K M) (fun i => emb (w i))
  rw [observationWitness]
  exact row

private theorem withTerms (d H K M state terms : OTerm α)
    (run : Nonempty (Derivation body Γ (grammarReport state d H K M)))
    (t : Nonempty (Derivation body Γ (termProjection terms state))) :
    Nonempty (Derivation body Γ (existingObservation d H K M)) := by
  apply programCases right ![state] _
  intro β j Δ args keep a
  rw [observationRename]
  rw [unaryTapeRename] at a
  have run' := renameInto run j Δ keep
  simp only [grammarReport,grammarTape,programRename,quadInputsRename] at run'
  have t' := renameInto t j Δ keep
  simp only [termProjection,unaryRename] at t'
  obtain ⟨a⟩ := a
  obtain ⟨run'⟩ := run'
  obtain ⟨t'⟩ := t'
  exact introduce (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    (state.relabel j) (terms.relabel j) args
    ⟨Derivation.conjunctionIntroduction run' (Derivation.conjunctionIntroduction t' a)⟩

private theorem withState (d H K M state : OTerm α)
    (run : Nonempty (Derivation body Γ (grammarReport state d H K M))) :
    Nonempty (Derivation body Γ (existingObservation d H K M)) := by
  apply programCases left ![state] _
  intro β j Δ terms keep t
  rw [observationRename]
  rw [unaryTapeRename] at t
  have run' := renameInto run j Δ keep
  simp only [grammarReport,grammarTape,programRename,quadInputsRename] at run'
  exact withTerms (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    (state.relabel j) terms run' t

/-- Exact original Program totality for the one coupled chosen grammar
observation, not totality of a new or numerically reflected model. -/
theorem obtainObservation (d H K M : OTerm α) :
    Nonempty (Derivation body Γ (existingObservation d H K M)) := by
  apply programCases selectedGrammar (grammarTape d H K M) _
  intro β j Δ state keep actual
  rw [observationRename]
  simp only [grammarTape,quadInputsRename] at actual
  exact withState (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) state actual

theorem observationCases (d H K M : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state terms args : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (observed (d.relabel j) (H.relabel j) (K.relabel j)
        (M.relabel j) state terms args)) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 3 := Sum.inl
  let phi := observationMatrix d H K M
  let Δ := phi :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 3 Γ phi goal (obtainObservation d H K M)
  exact next _ j Δ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
