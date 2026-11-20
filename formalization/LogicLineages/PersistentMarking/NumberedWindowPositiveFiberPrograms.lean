module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion

/-- Read the same unary field at the original source or destination coordinate.
The certificate is coordinate 1 and is never consulted by either guard. -/
def atInput (a : Program 1) (i : Fin 3) : Program 3 :=
  .composition a (fun _ => .projection i)

def agree (a : Program 1) : Program 3 :=
  .composition InternalEqualityTest.equalityTest ![atInput a 0,atInput a 2]

/-- An explicit choice of scalar certificate program. Keep the supplied
positive-path test verbatim as the last of three exact-one conjuncts. -/
def guarded (ctx ty : Program 1) (r : Program 3) : Program 3 :=
  InternalAcceptance.conjunction (agree ctx)
    (InternalAcceptance.conjunction (agree ty) r)

end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberPrograms
