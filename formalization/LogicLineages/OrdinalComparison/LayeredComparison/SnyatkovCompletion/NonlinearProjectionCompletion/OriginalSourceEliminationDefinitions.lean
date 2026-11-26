module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceElimination
open CommonLayerSyntax

/-- Literal inclusion of the original f-only term syntax. The expanded grammar
itself remains unchanged, including its actual H and inverse constructors. -/
def embed : BaseTerm → Term
  | .numeral n => .numeral n
  | .variable i => .variable i
  | .add a b => .add (embed a) (embed b)
  | .phi a => .phi (embed a)

def graphNames (i : Nat) (p : Matrix) : List Nat :=
  ExpandedBooleanGraph.allocated [i] p
def binderBlock (i : Nat) (p : Matrix) : List Nat := i :: graphNames i p
def graphFormula (i : Nat) (p : Matrix) : NormalForm.Formula :=
  ExpandedBooleanGraph.compile [i] p

/-- The actual initializer and bound-length projector consume the entire
functional graph. No semantic witness or numeric solver is an argument. -/
def eliminateBinder (i : Nat) (p : Matrix) : Matrix :=
  WholeBoundInitialization.project (binderBlock i p) (graphFormula i p)

/-- Structural recursion on the ORIGINAL source syntax, including arbitrary
negation, quantifier nesting and raw-name shadowing. Numeric computability of
this concrete compiler is a separate obligation, not a field of this definition. -/
def eliminate : SourceFormula → Matrix
  | .equal a b => .equal (embed a) (embed b)
  | .less a b => .less (embed a) (embed b)
  | .negative p => .negative (eliminate p)
  | .conjunction p q => .conjunction (eliminate p) (eliminate q)
  | .existsNat i p => eliminateBinder i (eliminate p)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceElimination
