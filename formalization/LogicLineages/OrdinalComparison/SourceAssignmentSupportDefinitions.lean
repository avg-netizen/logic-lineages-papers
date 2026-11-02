module
public import LogicLineages.OrdinalComparison.TrackedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AssignmentSupport
open SourceFreeOccurrences

def componentName {Γ : List Ty} (c : OrdinalComponent Γ) : PackedVariable Γ := ⟨c.1,c.2.1⟩
/-- Literal actual occurring typed names; order and duplicates remain available.
No semantic dependence or independent valuation test replaces occurrence. -/
def names {Γ : List Ty} (t : OrdinalExpression Γ) : List (PackedVariable Γ) :=
  (ordinalExpressionVariables t).map componentName

def Supported {Γ : List Ty} (S : List (PackedVariable Γ)) (t : OrdinalExpression Γ) : Prop :=
  ∀x∈names t,x∈S
end LogicLineages.OrdinalComparison.Source.AssignmentSupport
