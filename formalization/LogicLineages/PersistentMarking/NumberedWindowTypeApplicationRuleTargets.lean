module
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleTargets
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets

def FormulaSubstitution : Prop :=
  ∀ (p : Program 3) (τ : Ty) (α β : Type) (q : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β),
    (formula p τ q).subst (fun a => arithmeticEmbedding.onTerm (ts a)) = formula p τ (q.subst ts)

def ApplicationElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (p : Program 3) (σ τ : Ty) (α : Type)
    (Γ : List (Formula α)) (q u v : OrdinaryArithmetic.Term α),
    Nonempty (Derivation body Γ (formula p (.arrow σ τ) q)) →
    Nonempty (Derivation body Γ (accepts p q u v)) →
    Nonempty (Derivation body Γ (formula p σ u)) →
    Nonempty (Derivation body Γ (formula p τ v))

def ApplicationIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (p : Program 3) (σ τ : Ty) (α : Type)
    (Γ : List (Formula α)) (q : OrdinaryArithmetic.Term α),
    let up : OrdinaryArithmetic.Term ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
    let vp : OrdinaryArithmetic.Term ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
    let qp := q.relabel (fun a => Sum.inl (Sum.inl a))
    Nonempty (Derivation body (formula p σ up :: accepts p qp up vp :: (Γ.map weaken).map weaken)
      (formula p τ vp)) → Nonempty (Derivation body Γ (formula p (.arrow σ τ) q))

end LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleTargets
