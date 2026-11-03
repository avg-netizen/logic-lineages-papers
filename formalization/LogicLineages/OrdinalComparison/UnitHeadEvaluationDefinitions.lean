module
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveDefinitions
public import LogicLineages.OrdinalComparison.EncodedDescentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitHeadEvaluation
open ForwardTranslation ScalarAnnotationData

/-- Literal common-unit substitution: every typed component becomes one.
Zero and collapse remain explicit and are refused by extractPositive. -/
def unitSyntax {Γ : List Ty} : OrdinalExpression Γ → OrdinalExpression Γ
  | .var _ => .one
  | .zero => .zero
  | .one => .one
  | .omega => .omega
  | .add a b => .add (unitSyntax a) (unitSyntax b)
  | .emul a b => .emul (unitSyntax a) (unitSyntax b)
  | .collapse a b => .collapse (unitSyntax a) (unitSyntax b)

def extractUnitHead {Γ : List Ty} (q : OrdinalExpression Γ) : Option ClosedPositive :=
  extractPositive (unitSyntax q)

def evaluateUnitHead {Γ : List Ty} (q : OrdinalExpression Γ) : Option NONote :=
  (extractUnitHead q).map ClosedPositive.evaluate

/-- No extra omega factor: normalize precisely the extracted positive syntax. -/
def normalCode (n : Nat) : Nat := encodedClosedPositive n
def finiteCode (n : Nat) : Bool := encodedFiniteTest (normalCode n)
def finiteValueCode (n : Nat) : Nat := encodedFiniteValue (normalCode n)
end LogicLineages.OrdinalComparison.Source.UnitHeadEvaluation
