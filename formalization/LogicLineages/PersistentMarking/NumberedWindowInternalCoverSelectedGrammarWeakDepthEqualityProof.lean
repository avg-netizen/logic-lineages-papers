module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthEqualityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnRelabel bindEmbedding liftBind varBind)
open ID1Completion.InternalControlGraphSupportProof (valueUnique equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalUnpair (left right)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (unaryInput)
open NumberedWindowInternalCoverSelectedGrammarTargets (selectedGrammar grammarTape)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedSubst)
open NumberedWindowInternalCoverSelectedGrammarWidthBaseProof (includeFromEquality)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets (depthAt)
open NumberedWindowInternalCoverSelectedGrammarDepthBindingProof (buildDepth)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveDepth (d D H K M state t a : OTerm α)
    (same : Derivation body Γ (eqn d D))
    (old : Derivation body Γ (observed d H K M state t a)) :
    Nonempty (Derivation body Γ (observed D H K M state t a)) := by
  let lift : α → α ⊕ Fin 1 := Sum.inl
  let clause : Formula (α ⊕ Fin 1) := observed (.var (.inr 0)) (H.relabel lift)
    (K.relabel lift) (M.relabel lift) (state.relabel lift) (t.relabel lift) (a.relabel lift)
  have atDepth (x : OTerm α) : instantiate clause (emb x) = observed x H K M state t a := by
    simp only [clause,lift,instantiate,bindEmbedding,observedSubst,liftBind,varBind]
  exact ⟨(atDepth D) ▸ Derivation.equalityElimination clause (emb d) (emb D) same ((atDepth d).symm ▸ old)⟩

private theorem equalAtReports (d D H K M old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn d D)))
    (small : Nonempty (Derivation body Γ (observed d H K M old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed D H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  obtain ⟨same⟩ := same
  obtain ⟨first⟩ := small
  obtain ⟨second⟩ := large
  obtain ⟨aligned⟩ := moveDepth d D H K M old oldTerms oldArgs same first
  have stateEq := valueUnique selectedGrammar old next (grammarTape D H K M)
    ⟨Derivation.conjunctionLeft aligned⟩ ⟨Derivation.conjunctionLeft second⟩
  have stateEquality : Nonempty (Derivation body Γ (equal old next)) := by
    rw [equalEqn]
    exact stateEq
  have pastRead := Derivation.conjunctionRight aligned
  have nextRead := Derivation.conjunctionRight second
  have observedT := unaryInput left oldTerms old next stateEquality ⟨Derivation.conjunctionLeft pastRead⟩
  have observedA := unaryInput right oldArgs old next stateEquality ⟨Derivation.conjunctionRight pastRead⟩
  have eqT := valueUnique left oldTerms nextTerms ![next] observedT ⟨Derivation.conjunctionLeft nextRead⟩
  have eqA := valueUnique right oldArgs nextArgs ![next] observedA ⟨Derivation.conjunctionRight nextRead⟩
  obtain ⟨tin⟩ := includeFromEquality oldTerms nextTerms eqT
  obtain ⟨ain⟩ := includeFromEquality oldArgs nextArgs eqA
  exact ⟨Derivation.conjunctionIntroduction tin ain⟩

theorem equalDepth (d D H K M : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn d D))) :
    Nonempty (Derivation body Γ (depthAt d D H K M)) := by
  apply buildDepth d D H K M
  intro β j Δ old oldTerms oldArgs next nextTerms nextArgs keep small large
  have he := renameInto same j Δ keep
  rw [eqnRelabel] at he
  exact equalAtReports (d.relabel j) (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    old oldTerms oldArgs next nextTerms nextArgs he small large

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthEqualityProof
