module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionDefinitions
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open LayeredComparison.SnyatkovCompletion

/-- Negate coefficients only. Every literal word occurrence remains. -/
def negateRow (r : Row) : Row := (-r.1,r.2.map (fun s => (-s.1,s.2)))

def rowEquation (r : Row) : Formula :=
  .conj (.atom (.nonnegative r)) (.atom (.nonnegative (negateRow r)))

def positiveRow (i : Nat) : Row := (-1,[(1,(i,[]))])

/-- Only original coordinates are positive. Fresh graph nodes remain natural. -/
def positiveFrame (n : Nat) : Formula :=
  (List.range n).foldr (fun i p => .conj (.atom (.nonnegative (positiveRow i))) p) .top

def rowEquations (rows : List Row) : Formula :=
  rows.foldr (fun r p => .conj (rowEquation r) p) .top

def badSignFormula (mode : Nat) (r : Row) : Formula :=
  if mode = 0 then .neg (.atom (.nonnegative (negateRow r)))
  else if mode = 1 then .atom (.nonnegative r)
  else .neg (rowEquation r)

/-- This Boolean constant does not erase the other disjunct's word domains. -/
def failedPositive (flag : Bool) : Formula := if flag then .bot else .top

/-- Literal formula for the existing package matrix. Keep the comparison row
in the second disjunct even when the first disjunct is already true. -/
def matrix (p : Pair.Package) : Formula :=
  .conj (positiveFrame p.1.2)
    (.conj (rowEquations p.2.2.1)
      (.disj (failedPositive p.2.2.2.2.2)
        (badSignFormula p.2.2.2.2.1 p.2.2.2.1)))

/-- Metadata which will be derived from the actual guarded source compiler.
It is not an input or oracle of any numerical decision procedure. -/
def PackageCertified (p : Pair.Package) : Prop :=
  3 ≤ p.1.1 ∧ p.2.1.Nodup ∧
  (∀ i < p.1.2, i ∈ p.2.1) ∧
  (∀ r ∈ p.2.2.1, RowAllowed p.1.1 r ∧
    ∀ i ∈ rowVariables r, i ∈ p.2.1) ∧
  RowAllowed p.1.1 p.2.2.2.1 ∧
  (∀ i ∈ rowVariables p.2.2.2.1, i ∈ p.2.1)

namespace Code

def nonnegative (r : Row) : Nat :=
  6 * Encodable.encode ((0,0,r) : WordLinearDecisionCompletion.Code.AtomData) + 2

def negative (p : Nat) : Nat := 6*p+3

def disjunction (p q : Nat) : Nat := 6 * Nat.pair p q + 5

def rowEquation (r : Row) : Nat :=
  LinearRows.Code.conjunction (nonnegative r) (nonnegative (negateRow r))

def positiveFrame (n : Nat) : Nat :=
  (List.range n).foldr (fun i p =>
    LinearRows.Code.conjunction (nonnegative (positiveRow i)) p) 0

def rowEquations (rows : List Row) : Nat :=
  rows.foldr (fun r p => LinearRows.Code.conjunction (rowEquation r) p) 0

def badSign (mode : Nat) (r : Row) : Nat :=
  if mode = 0 then negative (nonnegative (negateRow r))
  else if mode = 1 then nonnegative r
  else negative (rowEquation r)

def failedPositive (flag : Bool) : Nat := if flag then 1 else 0

def matrix (p : Pair.Package) : Nat :=
  LinearRows.Code.conjunction (positiveFrame p.1.2)
    (LinearRows.Code.conjunction (rowEquations p.2.2.1)
      (disjunction (failedPositive p.2.2.2.2.2)
        (badSign p.2.2.2.2.1 p.2.2.2.1)))

end Code

/-- Bind the accepted actual closed-word solver, at the package's own degree. -/
noncomputable def packageCounterexample (p : Pair.Package) : Bool :=
  ClosedWordDecisionCompletion.Machine.solve p.1.1 (Code.matrix p)

/-- Literal guarded original-source compilation; rejection is explicit. -/
noncomputable def decision (q : SourceCode.Input) : Option Bool :=
  (Admission.compile q).map (fun p => !(packageCounterexample p))

/-- A total numerical Boolean function. Outside the admitted original class,
false is merely the documented default, not a source-semantics assertion. -/
noncomputable def solve (q : SourceCode.Input) : Bool := (decision q).getD false

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion
