module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRT
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalCoprimeMultiple
/-- A single residue satisfying the original relation and congruent to c modulo m. -/
def chosen {α : Type} (R : Formula (α ⊕ Fin 1)) (m c : OTerm α) : Formula α :=
  existsOne (R ⊓ arithmeticEmbedding.onFormula
    (InternalModularArithmetic.congruent (c.relabel Sum.inl) (.var (.inr 0)) (m.relabel Sum.inl)))
/-- Each index below the object bound has an original relation witness. -/
def availableBelow {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  bounded (existsOne R) n
/-- The residue witness may depend on the index; the code c is shared. -/
def residuesBelow {α : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (c n : OTerm α) : Formula α :=
  bounded (chosen R (suc t) (c.relabel Sum.inl)) n
/-- One code is existentially bound before all indices and their residue witnesses. -/
def solution {α : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  existsOne (residuesBelow (t.relabel (Sum.map Sum.inl id))
    (R.relabel (Sum.map (Sum.map Sum.inl id) id)) (.var (.inr 0)) (n.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRT
