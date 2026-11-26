module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundWitnessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn liftBind varBind bindEmbedding)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderTransitivity actualOriginalOrderIrreflexivity)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalQuotientComparisonSyntaxProof (orderInstantiate)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open NumberedWindowInternalSparseMinimumBoundTargets
open NumberedWindowInternalSparseMinimumBoundSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem enter (code k val : OTerm α) (d : Nonempty (Derivation body Γ (boundedRow code k val))) :
    Nonempty (Derivation body Γ (boundedWitness code k)) := by
  obtain ⟨d⟩ := d
  rw [witnessUnfold]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb val)
  rwa [binderValue]

theorem casesValue (code k : OTerm α) (goal : Formula α)
    (input : Nonempty (Derivation body Γ (boundedWitness code k)))
    (finish : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (boundedRow (code.relabel j) (k.relabel j) w)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  rw [witnessUnfold] at input
  obtain ⟨d⟩ := input
  let Δ := boundBinder code k :: Γ.map weaken
  obtain ⟨applied⟩ := finish (α ⊕ Fin 1) Sum.inl Δ (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination d applied⟩

theorem candidateTransport (code a b : OTerm α)
    (equ : Derivation body Γ (eqn a b)) (proof : Nonempty (Derivation body Γ (boundedWitness code a))) :
    Nonempty (Derivation body Γ (boundedWitness code b)) := by
  let θ : Formula (α ⊕ Fin 1) := boundedWitness (code.relabel Sum.inl) (.var (.inr 0))
  have inst (t : OTerm α) : instantiate θ (emb t) = boundedWitness code t := by
    simp only [θ,instantiate,bindEmbedding,witnessSubst,liftBind,varBind]
  obtain ⟨d⟩ := proof
  have moved := Derivation.equalityElimination θ (emb a) (emb b) equ (by rw [inst]; exact d)
  rw [inst] at moved
  exact ⟨moved⟩

theorem transportBound (candidate a b : OTerm α) (equ : Derivation body Γ (eqn a b))
    (d : Derivation body Γ (ltF candidate a).not) :
    Nonempty (Derivation body Γ (ltF candidate b).not) := by
  let θ : Formula (α ⊕ Fin 1) := (ltF (candidate.relabel Sum.inl) (.var (.inr 0))).not
  have inst (t : OTerm α) : instantiate θ (emb t) = (ltF candidate t).not := by
    change (instantiate (ltF (candidate.relabel Sum.inl) (.var (.inr 0))) (emb t)).not = _
    simp only [orderInstantiate,liftBind,varBind]
  have moved := Derivation.equalityElimination θ (emb a) (emb b) equ (by rw [inst]; exact d)
  rw [inst] at moved
  exact ⟨moved⟩

theorem irrefl (a : OTerm α) : Nonempty (Derivation body Γ (ltF a a).not) := by
  obtain ⟨d⟩ := actualOriginalOrderIrreflexivity body α a
  exact ⟨weakenClosed d Γ⟩

theorem restrict (k h p : OTerm α) (old : Derivation body Γ (ltF k p).not)
    (small : Derivation body Γ (ltF h p)) : Nonempty (Derivation body Γ (ltF k h).not) := by
  obtain ⟨tr⟩ := actualOriginalOrderTransitivity body α k h p
  let hyp := ltF k h
  have step : Derivation body (hyp :: Γ) (ltF k p) := Derivation.implicationElimination
    (weakenClosed tr (hyp :: Γ)) (Derivation.conjunctionIntroduction
      (Derivation.hypothesis List.mem_cons_self) (addHyp small hyp))
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp old hyp) step)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundWitnessProof
