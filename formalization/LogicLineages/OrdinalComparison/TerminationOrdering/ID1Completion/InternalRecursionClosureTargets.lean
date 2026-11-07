module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalRecursionTotality : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))),
  Total body f → Total body g → Total body (OrdinaryArithmetic.recursionGraph f g)

/-- At-most-one closure requires no totality hypothesis on either relation. -/
def ActualOriginalRecursionFunctionality : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (f : OFormula (Fin (n+1)))
    (g : OFormula (Fin (n+3))),
  Functional body f → Functional body g →
    Functional body (OrdinaryArithmetic.recursionGraph f g)

/-- Every original program constructor, including Program.recursion, has
unrestricted internal totality and functionality of its literal graph. -/
def ActualOriginalPrograms : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (p : Program n),
  Total body (OrdinaryArithmetic.graphFormula p) ∧
    Functional body (OrdinaryArithmetic.graphFormula p)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureTargets
