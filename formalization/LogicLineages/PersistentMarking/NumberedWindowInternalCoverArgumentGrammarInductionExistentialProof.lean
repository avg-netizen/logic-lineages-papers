module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding varBind)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction actualFiniteExistentialElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets (ArgumentHit)
open NumberedWindowInternalCoverArgumentGrammarInductionBindingProof (argumentWitness argumentExistsSubst)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem introduceArgument (F : Program 1) (s : Settings) (raw p d w state terms args : OTerm α)
    (measure : Nonempty (Derivation body Γ (unary (argumentMeasure F) p raw)))
    (pair : Nonempty (Derivation body Γ (codePair p d w)))
    (placed : ArgumentHit s body Γ d w state terms args raw) :
    Nonempty (Derivation body Γ (argumentExists F s raw)) := by
  let vals : Fin 6 → OTerm α := ![p,d,w,state,terms,args]
  apply actualFiniteExistentialIntroduction body α 6 Γ (argumentMatrix F s raw) (fun i => emb (vals i))
  rw [argumentWitness]
  obtain ⟨m⟩ := measure
  obtain ⟨cp⟩ := pair
  obtain ⟨obs⟩ := placed.scope
  obtain ⟨hit⟩ := placed.hit
  exact ⟨Derivation.conjunctionIntroduction m
    (Derivation.conjunctionIntroduction cp (Derivation.conjunctionIntroduction obs hit))⟩

theorem consumeArgument (F : Program 1) (s : Settings) (raw : OTerm α) (goal : Formula α)
    (actual : Nonempty (Derivation body Γ (argumentExists F s raw)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (p d w state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary (argumentMeasure F) p (raw.relabel j))) →
      Nonempty (Derivation body Δ (codePair p d w)) →
      ArgumentHit s body Δ d w state terms args (raw.relabel j) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 6 := Sum.inl
  let vals : Fin 6 → OTerm (α ⊕ Fin 6) := fun i => .var (.inr i)
  let P := argumentMatrix F s raw
  let Δ := P :: Γ.map (fun q => q.relabel j)
  apply actualFiniteExistentialElimination body α 6 Γ P goal actual
  have hs : Derivation body Δ (argumentPayload F s (raw.relabel j) vals) :=
    Derivation.hypothesis List.mem_cons_self
  have data := Derivation.conjunctionRight hs
  have scope := Derivation.conjunctionRight data
  have keep (q : Formula α) (h : q ∈ Γ) : q.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  exact next _ j Δ (vals 0) (vals 1) (vals 2) (vals 3) (vals 4) (vals 5) keep
    ⟨Derivation.conjunctionLeft hs⟩ ⟨Derivation.conjunctionLeft data⟩
    ⟨⟨Derivation.conjunctionLeft scope⟩,⟨Derivation.conjunctionRight scope⟩⟩

theorem transportArgument (F : Program 1) (s : Settings) (raw key : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn raw key)))
    (actual : Nonempty (Derivation body Γ (argumentExists F s raw))) :
    Nonempty (Derivation body Γ (argumentExists F s key)) := by
  obtain ⟨eq⟩ := eq
  obtain ⟨actual⟩ := actual
  have moved := Derivation.equalityElimination
    (argumentExists F s (.var (.inr (0 : Fin 1)))) (emb raw) (emb key) eq
  simp only [instantiate,bindEmbedding,argumentExistsSubst,varBind] at moved
  exact ⟨moved actual⟩

#print axioms introduceArgument
#print axioms consumeArgument
#print axioms transportArgument

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
