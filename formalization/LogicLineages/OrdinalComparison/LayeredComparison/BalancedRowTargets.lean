module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Targets
/-- Derive ALL full-basis affine bounds from literal signed-row data. No
independent input window or missing basis coordinate is supplied as an oracle. -/
def ActualBasisBounds:Prop:=∀basis:List Nat,∀row:Row,wellFormed basis row→
  ∀a∈row.atoms,basis.sum ≤ input basis a.2∧
    input basis a.2 ≤ multiplierMaximum row*basis.sum+offsetMaximum row∧
    actualOrdinalNorm a.2.head.1.repr ≤ normMaximum row

def ActualRemainderBound:Prop:=∀basis:List Nat,∀row:Row,wellFormed basis row→
  (remainderValue basis row).natAbs ≤ row.constant.natAbs+outsideMaximum row*basis.sum

/-- The EXACT original L yields the genuine finite-family head window, and
bounds the outside remainder against EVERY surviving input, even if all larger
blocks later cancel. No common-head restriction is imposed on the atoms. -/
def ActualLargeWindow:Prop:=∀basis:List Nat,∀row:Row,wellFormed basis row→
  (∀a∈row.atoms,threshold row ≤ input basis a.2)→
  ∀selected∈row.atoms,(∀a∈row.atoms,input basis selected.2 ≤ input basis a.2)→
  (∀a∈row.atoms,actualOrdinalNorm a.2.head.1.repr+2 ≤ input basis selected.2∧
    input basis selected.2 ≤ input basis a.2∧input basis a.2 < Phi (input basis selected.2))∧
  ∀a∈row.atoms,4*(remainderValue basis row).natAbs < input basis a.2*input basis a.2

/-- One small COMPLETE argument bounds the ENTIRE shared basis, including
entries used only by the open outside remainder. The later raw-variable box
consumer must separately prove actual source support domination. -/
def ActualSmallBasisBound:Prop:=∀basis:List Nat,∀row:Row,wellFormed basis row→
  ∀a∈row.atoms,input basis a.2 < threshold row→
    basis.sum < threshold row∧∀x∈basis,x < threshold row
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Targets
