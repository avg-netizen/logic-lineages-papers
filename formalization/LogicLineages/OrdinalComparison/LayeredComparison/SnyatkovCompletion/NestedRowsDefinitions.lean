module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRows
open NormalForm

/-- Both natural truncations are literal, including negative inner inputs. -/
def replacement (j : Nat) (a b : Int) (ν : Nat → Nat) : Nat :=
  ((((ν j : Int) + a).toNat : Int) + b).toNat

def substitute (i j : Nat) (a b : Int) (p : Formula) : Formula :=
  .disjunction
    (.conjunction (SignedRows.anchorDomain j a) (SignedRows.substitute i j (a + b) p))
    (.conjunction (.negative (SignedRows.anchorDomain j a)) (BoundedRows.substitute i b.toNat p))

namespace Code
abbrev Input := (Nat × Nat) × (Int × Int)
def input (i j : Nat) (a b : Int) : Input := ((i, j), (a, b))
def substitute (i j : Nat) (a b : Int) (code : Nat) : Nat :=
  SignedRows.Code.disjunction
    (SignedRows.Code.conjunction (SignedRows.Code.anchorDomain j a)
      (SignedRows.Code.substitute i j (a + b) code))
    (SignedRows.Code.conjunction (SignedRows.Code.negative (SignedRows.Code.anchorDomain j a))
      (BoundedRows.Code.formula i b.toNat code))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRows
