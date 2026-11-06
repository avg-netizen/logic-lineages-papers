module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRT
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalCoprimeMultiple
/-- Triangular bounded pairwise coprimality: for all j<n and i<j,
    the literal positive moduli succ(t(j)) and succ(t(i)) are coprime. -/
def pairwiseBelow {α : Type} (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  bounded (coprimeBelow (suc t) (t.relabel (Sum.map Sum.inl id)) (.var (.inr 0))) n
/-- One fixed c realizes every residue at every object index below n. -/
def residuesBelow {α : Type} (t r : OTerm (α ⊕ Fin 1)) (c n : OTerm α) : Formula α :=
  bounded (arithmeticEmbedding.onFormula
    (InternalModularArithmetic.congruent (c.relabel Sum.inl) r (suc t))) n
/-- The single code is quantified outside the bounded universal. -/
def solution {α : Type} (t r : OTerm (α ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  existsOne (residuesBelow (t.relabel (Sum.map Sum.inl id))
    (r.relabel (Sum.map Sum.inl id)) (.var (.inr 0)) (n.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRT
