module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveSentenceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundAboveProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename packedBodyRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenSingletonLambdaRow)
open NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof (boundTermRename)
open NumberedWindowInternalLiteralSingletonBoundOpenAboveSentenceProof
  (aboveBody aboveResult exact_OpenSingletonBoundAboveExists)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem numeralRename {β : Type} (n : Nat) (r : α → β) :
    (numeral n : OTerm α).relabel r = numeral n := by
  induction n with
  | zero => exact zRelabel r
  | succ n ih =>
    simpa only [numeral,sucRelabel] using
      congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

private theorem rawLambdaTermRename {β : Type} (ty b : OTerm α) (r : α → β) :
    (rawLambdaTerm ty b).relabel r = rawLambdaTerm (ty.relabel r) (b.relabel r) := by
  simp only [rawLambdaTerm,rawConsRename,numeralRename,packedBodyRename,List.map_cons,List.map_nil]

/-- The two conjuncts of the sentence matrix, in any context over the
extended variables. -/
theorem aboveBodyParts {Θ : List (Formula (α ⊕ Fin 1))}
    (V : Program 1) (H : Program 2) (U : Program 3) (a d t i : OTerm α)
    (held : D B Θ (aboveBody V H U a d t i)) :
    D B Θ (eqn (i.relabel Sum.inl) (suc (Term.var (Sum.inr 0)))) ∧
    D B Θ (programGraph (singletonBound V H U)
      (suc (boundTerm (t.relabel Sum.inl) (Term.var (Sum.inr 0))))
      ![a.relabel Sum.inl,d.relabel Sum.inl,boundTerm (t.relabel Sum.inl) (i.relabel Sum.inl)]) := by
  obtain ⟨held⟩ := held
  unfold aboveBody at held
  exact ⟨⟨Derivation.conjunctionLeft held⟩,⟨Derivation.conjunctionRight held⟩⟩

/-- Elimination of the existence sentence by the calculus rule for the
existential quantifier. A derivation of the sentence, however obtained,
gives the continuation the lowered index as the fresh variable, with the
successor equation and the actual `singletonBound` graph. -/
theorem exact_OpenSingletonBoundAboveSentenceCases (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α) (goal : Formula α)
    (held : D B Γ (aboveResult V H U a d t i))
    (use : ∀ (β : Type) (r : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel r ∈ Δ) →
      D B Δ (eqn (i.relabel r) (suc j)) →
      D B Δ (programGraph (singletonBound V H U) (suc (boundTerm (t.relabel r) j))
        ![a.relabel r,d.relabel r,boundTerm (t.relabel r) (i.relabel r)]) →
      D B Δ (goal.relabel r)) : D B Γ goal := by
  obtain ⟨held⟩ := held
  unfold aboveResult at held
  have parts := aboveBodyParts (B := B) (Θ := aboveBody V H U a d t i :: Γ.map weaken)
    V H U a d t i ⟨Derivation.hypothesis List.mem_cons_self⟩
  have inner : D B (aboveBody V H U a d t i :: Γ.map weaken) (weaken goal) :=
    use (α ⊕ Fin 1) Sum.inl (aboveBody V H U a d t i :: Γ.map weaken) (Term.var (Sum.inr 0))
      (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)) parts.1 parts.2
  obtain ⟨inner⟩ := inner
  exact ⟨Derivation.existentialElimination held inner⟩

/-- Lambda row over a bound-variable body above the bumped depth. The child
premise of `exact_OpenSingletonLambdaRow` is discharged by the existence
sentence at depth `suc d`: the child is the actual `singletonBound` on the
body, and its successor-packed output is the lowered node. The continuation
receives the rebuilt lambda node as the output of the installed program. -/
theorem exact_OpenSingletonLambdaBoundAbove (V : Program 1) (H : Program 2) (W : Program 3)
    (a d ty t i : OTerm α) (goal : Formula α)
    (inserted : D B Γ (unary V (suc z) a))
    (lambdaNode : D B Γ (unary V (suc z) (rawLambdaTerm ty (boundTerm t i))))
    (boundNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (above : D B Γ (ltF (suc d) i))
    (use : ∀ (β : Type) (r : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel r ∈ Δ) →
      D B Δ (eqn (i.relabel r) (suc j)) →
      D B Δ (programGraph (singletonLambda V H (singletonBound V H W))
        (suc (rawLambdaTerm (ty.relabel r) (boundTerm (t.relabel r) j)))
        ![a.relabel r,d.relabel r,
          rawLambdaTerm (ty.relabel r) (boundTerm (t.relabel r) (i.relabel r))]) →
      D B Δ (goal.relabel r)) : D B Γ goal := by
  apply exact_OpenSingletonBoundAboveSentenceCases V H W a (suc d) t i goal
    (exact_OpenSingletonBoundAboveExists V H W a (suc d) t i inserted boundNode above)
  intro β r Δ j keep same child
  rw [sucRelabel] at child
  have inserted' : D B Δ (unary V (suc z) (a.relabel r)) := by
    have moved := renameInto inserted r Δ keep
    rw [unaryRename,sucRelabel,zRelabel] at moved
    exact moved
  have lambdaNode' : D B Δ (unary V (suc z)
      (rawLambdaTerm (ty.relabel r) (boundTerm (t.relabel r) (i.relabel r)))) := by
    have moved := renameInto lambdaNode r Δ keep
    rw [unaryRename,sucRelabel,zRelabel,rawLambdaTermRename,boundTermRename] at moved
    exact moved
  exact use β r Δ j keep same
    (exact_OpenSingletonLambdaRow V H (singletonBound V H W) (a.relabel r) (d.relabel r)
      (ty.relabel r) (boundTerm (t.relabel r) (i.relabel r)) (boundTerm (t.relabel r) j)
      inserted' lambdaNode' child)

#print axioms aboveBodyParts
#print axioms exact_OpenSingletonBoundAboveSentenceCases
#print axioms exact_OpenSingletonLambdaBoundAbove
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundAboveProof
