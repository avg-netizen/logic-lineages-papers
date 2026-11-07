module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationTargets

/-- The original checker is zero or one on EVERY natural input vector,
including malformed context, endpoint and certificate codes. -/
def ActualPositiveRange : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4),
    ContextUniform.positiveValue n arity v = 0 ∨
    ContextUniform.positiveValue n arity v = 1

/-- Exact semantic typed-successor preservation for the ORIGINAL checker.
The target object y and numeric type typ are unchanged; validWindow is the
only restriction on the raw natural context code. The arity, decoded symbol
window, precedence table, ambient Gamma and certificate are arbitrary. -/
def ActualTypedSuccessor : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context typ x y certificate : Nat),
    GuardCalibration.validWindow n context = 1 →
    JointGammaTyped.typedValue n arity (List.Vector.ofFn ![context,typ,x]) = 1 →
    ContextUniform.positiveValue n arity (List.Vector.ofFn ![context,x,y,certificate]) = 1 →
    JointGammaTyped.typedValue n arity (List.Vector.ofFn ![context,typ,y]) = 1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationTargets
