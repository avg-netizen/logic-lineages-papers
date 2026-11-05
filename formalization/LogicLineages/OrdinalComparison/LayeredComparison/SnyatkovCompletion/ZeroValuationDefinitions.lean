module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuation
open NormalForm

/-- Evaluate every literal summand at zero with the existing actual hierarchy. -/
def projectRow (r : Row) : Row :=
  (r.1 + (r.2.map (fun a => a.1 * (BoundedRows.valueAt a.2 0 : Int))).sum, [])
def projectAtom : Atom → Atom
  | .nonnegative r => .nonnegative (projectRow r)
  | .divisible m r => .divisible m (projectRow r)
def project : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (projectAtom a)
  | .negative p => .negative (project p)
  | .conjunction p q => .conjunction (project p) (project q)
  | .disjunction p q => .disjunction (project p) (project q)
def evaluate (p : Formula) : Bool := ClosedLinear.evaluateConstants (project p)

namespace Code
def projectRow (r : NormalForm.Code.RowData) : NormalForm.Code.RowData :=
  (r.1 + (r.2.map (fun a => a.1 * (BoundedRows.Code.itemValue a.2 0 : Int))).sum, [])
def projectAtom (a : NormalForm.Code.AtomData) : NormalForm.Code.AtomData :=
  (a.1, a.2.1, projectRow a.2.2)
def project (code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (fun a => Encodable.encode (projectAtom (LinearRows.Code.decodeAtom a))) code
def evaluate (code : Nat) : Bool := ClosedLinear.Code.evaluateConstants (project code)
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuation
