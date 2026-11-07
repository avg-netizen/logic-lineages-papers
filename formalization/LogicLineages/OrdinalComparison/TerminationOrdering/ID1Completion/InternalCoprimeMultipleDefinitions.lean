module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultiple
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalOriginalOrderSyntaxProof InternalBezoutExistenceTargets
/-- The literal bounded universal, with the bound an object term. -/
def bounded {α : Type} (p : Formula (α ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  allOne ((ltF (.var (.inr 0)) (n.relabel Sum.inl)).imp p)
/-- All members of the positive term-defined family are coprime to a. -/
def coprimeBelow {α : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  bounded (coprime (a.relabel Sum.inl) (suc t)) n
/-- Every member of the same family divides P. -/
def dividesBelow {α : Type} (t : OTerm (α ⊕ Fin 1)) (P n : OTerm α) : Formula α :=
  bounded (arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc t) (P.relabel Sum.inl))) n
/-- P is represented by succ(p), so positivity is literal and unguarded. -/
def commonMultiple {α : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  existsOne (coprime (a.relabel Sum.inl) (suc (.var (.inr 0))) ⊓
    dividesBelow (t.relabel (Sum.map Sum.inl id)) (suc (.var (.inr 0))) (n.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultiple
