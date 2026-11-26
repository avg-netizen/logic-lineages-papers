module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentationDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutput

open LogicLineages.OrdinalComparison.Source GroundEquivalence
open OriginalInput (Query)
open RawSourceDAG (Code)
open RawSourceDAG.PlanComparison (OutputCode)

def asTreeQuery (strict : Bool) (pair : Code × Code) : Query :=
  (pair.1.1.length,strict,CurrentTreeCode.expand pair.1,CurrentTreeCode.expand pair.2)

def outputQueries (out : OutputCode) : Query × Query :=
  (asTreeQuery true out.1,asTreeQuery false out.2)

noncomputable def toGroundTrees (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : Query) :
    Option (Query × Query) :=
  (CurrentDecisionTreePresentation.toGround p f q).map outputQueries

/-- Independent typed comparator for literal emitted original tree queries. -/
def literal (strict : Bool) {Γ : List Ty} (a b : Input Γ .ground) : Query :=
  (Γ.length,strict,SyntaxCode.encodeTerm a.term,SyntaxCode.encodeTerm b.term)

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutput
