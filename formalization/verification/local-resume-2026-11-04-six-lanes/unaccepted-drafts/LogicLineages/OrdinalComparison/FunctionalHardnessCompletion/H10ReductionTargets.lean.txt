module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10ReductionTargets

/-- Exact cross-lane supplier contract. The input is S1's unchanged explicit
integer-polynomial code with zero-allowing natural roots. The output is S5's
well-formed finite fixed-coefficient linear system with unknowns in N[X].
Malformed inputs must be handled by the one total computable map. No H10 or
polynomial-system undecidability premise is a field of this reduction. -/
def CodedH10ToLinearSystems : Prop :=
  ∃ reduce : Nat → Nat, Computable reduce ∧ ∀ e : Nat,
    LogicLineages.ComputabilityKnowledge.DiophantineCompletion.encodedPolynomialSolvable e ↔
      encodedPolynomialSolvable (reduce e)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10ReductionTargets
