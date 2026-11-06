module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphComposition
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
abbrev OTerm (α : Type) := OrdinaryArithmetic.Term α
abbrev OFormula (α : Type) := OrdinaryArithmetic.Formula α

def graph {n : Nat} {α : Type} (f : OFormula (Fin (n+1))) (out : OTerm α)
    (xs : Fin n → OTerm α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.applyGraph f out xs)

def matrix {m n : Nat} {α : Type} (f : OFormula (Fin (n+1)))
    (g : Fin n → OFormula (Fin (m+1))) (out : OTerm α) (xs : Fin m → OTerm α) :
    OFormula (α ⊕ Fin n) :=
  OrdinaryArithmetic.applyGraph f (out.relabel Sum.inl) (fun i => .var (.inr i)) ⊓
    OrdinaryArithmetic.andFin (fun i => OrdinaryArithmetic.applyGraph (g i) (.var (.inr i))
      (fun j => (xs j).relabel Sum.inl))

/-- Actual proof trees for every term instance of output existence. This is
an explicit premise, not an assertion that arbitrary graph formulas have it. -/
def Total (body : Positive (Fin 1)) {n : Nat} (f : OFormula (Fin (n+1))) : Prop :=
  ∀ (α : Type) (xs : Fin n → OTerm α),
    Nonempty (Derivation body [] (existsOne (graph f (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl))))

/-- Actual proof trees for every term instance of output uniqueness. -/
def Functional (body : Positive (Fin 1)) {n : Nat} (f : OFormula (Fin (n+1))) : Prop :=
  ∀ (α : Type) (out other : OTerm α) (xs : Fin n → OTerm α),
    Nonempty (Derivation body [] ((graph f out xs ⊓ graph f other xs).imp
      (arithmeticEmbedding.onFormula (out.equal other))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphComposition
