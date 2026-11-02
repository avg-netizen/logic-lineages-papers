module
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeRow
abbrev Row := List (Int×Nat)
def mass (row : Row) : Nat := (row.map (fun a => a.1.natAbs)).sum
/-- Exactly the threshold printed in the common-head proof, not a larger
sum of independent coefficient and constant bounds. -/
def threshold (K : Int) (row : Row) : Nat := max 4 (max (2*mass row) (4*K.natAbs+4))
noncomputable def value (lam : Ordinal) (K : Int) (row : Row) : Int :=
  K+(row.map (fun a => a.1*(actualHeadValue lam a.2 : Int))).sum
abbrev NumericalRow := List (Int×Nat×Nat)
def numericalMass (row : NumericalRow) : Nat := (row.map (fun a => a.1.natAbs)).sum
def numericalThreshold (K : Int) (row : NumericalRow) := max 4 (max (2*numericalMass row) (4*K.natAbs+4))
def numericalValue (K : Int) (row : NumericalRow) := K+(row.map (fun a => a.1*(a.2.1 : Int))).sum
noncomputable def predecessorIndex (lam : Ordinal) (t : Nat) := (Phi^[actualHeadCount lam t-1]) t
noncomputable def numerical (lam : Ordinal) (row : Row) : NumericalRow :=
  row.map fun a => (a.1,actualHeadValue lam a.2,predecessorIndex lam a.2)
end LogicLineages.OrdinalComparison.CommonHeadLargeRow
