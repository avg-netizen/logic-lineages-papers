module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitness
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
abbrev OTerm (α : Type) := OrdinaryArithmetic.Term α
def modulus {α : Type} (b i : OTerm α) : OTerm α :=
  OrdinaryArithmetic.succTerm (OrdinaryArithmetic.mulTerm (OrdinaryArithmetic.succTerm i) b)
def equations {α : Type} (a b i r q d : OTerm α) : OrdinaryArithmetic.Formula α :=
  a.equal (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm q (modulus b i)) r) ⊓
    (OrdinaryArithmetic.addTerm r (OrdinaryArithmetic.succTerm d)).equal (modulus b i)
def matrix {α : Type} (a b i r : OTerm α) : OrdinaryArithmetic.Formula (α ⊕ Fin 2) :=
  equations (a.relabel Sum.inl) (b.relabel Sum.inl) (i.relabel Sum.inl) (r.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitness
