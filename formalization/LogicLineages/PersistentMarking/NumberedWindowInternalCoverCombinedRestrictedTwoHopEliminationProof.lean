module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopEliminationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparsePathEnvelopeTargets (hopCodeTerm edgeCodeTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
attribute [local irreducible] programGraph

variable {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

theorem hopDataRename {β : Type} (ctx cod src wr dst left right : OTerm α) (j : α → β) :
    (thinHopData C X W s raw ctx cod src wr dst left right).relabel j = thinHopData C X W s raw
      (ctx.relabel j) (cod.relabel j) (src.relabel j) (wr.relabel j) (dst.relabel j)
      (left.relabel j) (right.relabel j) := by
  simp only [thinHopData,conjunctionRename,leastRename,positiveRename,singletonCertificate,hopCodeTerm,
    edgeCodeTerm,rawConsRename,sucRelabel,zRelabel]

theorem thinProvidedCases {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (ctx cod src wr dst : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr dst)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (left right : OTerm β),
      (∀ a ∈ Γ, a.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (thinHopData C X W s raw (ctx.relabel j) (cod.relabel j)
        (src.relabel j) (wr.relabel j) (dst.relabel j) left right)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 2 := Sum.inl
  let row := thinHopRow C X W s raw ctx cod src wr dst
  let Δ := row :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 2 Γ row goal known
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have here : Nonempty (Derivation body Δ row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact k (α ⊕ Fin 2) j Δ (.var (.inr 0)) (.var (.inr 1)) keep here

#print axioms hopDataRename
#print axioms thinProvidedCases
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopEliminationProof
