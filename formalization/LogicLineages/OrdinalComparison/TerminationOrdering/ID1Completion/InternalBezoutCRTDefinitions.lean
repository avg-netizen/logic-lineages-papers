module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRT
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
abbrev OTerm (α : Type) := OrdinaryArithmetic.Term α
abbrev add {α : Type} := @OrdinaryArithmetic.addTerm α
abbrev mul {α : Type} := @OrdinaryArithmetic.mulTerm α
abbrev suc {α : Type} := @OrdinaryArithmetic.succTerm α
/-- An explicit oriented natural-number Bézout certificate, not a coprimality hypothesis. -/
def certificate {α : Type} (a n u v : OTerm α) : OrdinaryArithmetic.Formula α :=
  (suc (mul u a)).equal (mul v (suc n))
/-- Polynomial combination with natural coefficients and no subtraction. -/
def combine {α : Type} (a n u r s : OTerm α) : OTerm α :=
  add (mul r (suc (mul u a))) (mul s (mul n (mul u a)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRT
