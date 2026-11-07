module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRT
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof
abbrev OTerm (α : Type) := OrdinaryArithmetic.Term α
/-- A simultaneous solution with one shared existentially bound natural variable. -/
def solution {α : Type} (a b r s : OTerm α) : Formula α :=
  existsOne
    (arithmeticEmbedding.onFormula
      (InternalModularArithmetic.congruent (.var (.inr 0)) (r.relabel Sum.inl) (a.relabel Sum.inl)) ⊓
     arithmeticEmbedding.onFormula
      (InternalModularArithmetic.congruent (.var (.inr 0)) (s.relabel Sum.inl) (b.relabel Sum.inl)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRT
