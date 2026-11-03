module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRowTargets
public import LogicLineages.OrdinalComparison.HeadWindowDefinitions
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow

def genuineHeads (row:Row):Prop:=∀a∈row.atoms,Order.IsSuccLimit a.2.head.1.repr
noncomputable def atomValue (basis:List Nat) (a:Atom):Nat:=
  actualHeadValue a.head.1.repr (input basis a)
noncomputable def atomEndpoint (basis:List Nat) (a:Atom):Nat:=
  actualHeadEndpoint a.head.1.repr (input basis a)
noncomputable def atomIndex (basis:List Nat) (a:Atom):Nat:=
  CommonHeadLargeRow.predecessorIndex a.head.1.repr (input basis a)
noncomputable def keyLess (basis:List Nat) (a b:Atom):Prop:=
  actualHeadKeyLess a.head.1.repr (input basis a) b.head.1.repr (input basis b)
noncomputable def keyEqual (basis:List Nat) (a b:Atom):Prop:=
  a.head.1.repr=b.head.1.repr∧input basis a=input basis b
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow
