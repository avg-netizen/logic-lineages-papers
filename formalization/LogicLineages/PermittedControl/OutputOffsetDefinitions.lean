module
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl

/-- Total signed coefficient code: even 2n denotes n; odd 2n+1 denotes -(n+1). -/
def signedOffsetValue (z : Nat) : Int :=
  if z%2=0 then (z/2 : Nat) else -((z/2+1 : Nat) : Int)

/-- Literal absolute-value margin on the explicit total signed encoding. -/
def outputOffsetTailCode (a b : Nat) : Nat := a/2+a%2+b/2+b%2+2

end LogicLineages.PermittedControl
