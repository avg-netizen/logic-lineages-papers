module
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment
def bound (n : Nat) : Nat := 1+((List.range n).map (fun j => Nat.pair j 0)).foldr max 0
def slot (xs : List Nat) (k : Nat) : Nat :=
  if k.unpair.2=0 then xs.getD k.unpair.1 0 else 0
def environment (xs : List Nat) : List Nat := (List.range (bound xs.length)).map (slot xs)
def rawValuation {Γ : List Ty} (xs : List Nat) (c : OrdinalComponent Γ) : Nat :=
  xs.getD (SourceTypedPorts.variableIndex c.2.1) 0
end LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment
