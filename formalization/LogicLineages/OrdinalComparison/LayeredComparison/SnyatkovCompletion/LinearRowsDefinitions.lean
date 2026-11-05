module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRows
open NormalForm
abbrev Sign := LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Sign
abbrev Boolean := LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean

def rowConst (z : Int) : Row := (z, [])
def rowAdd (r s : Row) : Row := (r.1 + s.1, r.2 ++ s.2)
def rowScale (z : Int) (r : Row) : Row :=
  (z * r.1, r.2.map (fun a => (z * a.1, a.2)))
def leading (i : Nat) (r : Row) : Int :=
  (r.2.map (fun a => if a.2.name = i then a.1 else 0)).sum
def remainder (i : Nat) (r : Row) : Row :=
  (r.1, r.2.filter (fun a => a.2.name != i))
def summandLinear (i : Nat) : Summand → Bool
  | .variable _ => true
  | .phi j _ | .hyperPhi j _ _ => j != i
def rowLinear (i : Nat) (r : Row) : Bool := r.2.all (fun a => summandLinear i a.2)
def atoms : Formula → List Atom
  | .truth | .falsity => []
  | .atom a => [a]
  | .negative p => atoms p
  | .conjunction p q | .disjunction p q => atoms p ++ atoms q

/-- Every occurrence is tested, even when its coefficient is zero. -/
def isLinear (i : Nat) (p : Formula) : Bool := (atoms p).all (fun a => rowLinear i a.row)

inductive UnitAtom where
  | nonnegative (sign : Sign) (row : Row)
  | divisible (modulusMinusOne : Nat) (sign : Sign) (row : Row)
abbrev UnitFormula := Boolean UnitAtom

def UnitAtom.row : UnitAtom → Row
  | .nonnegative _ r | .divisible _ _ r => r
def UnitAtom.eval (ν : Nat → Nat) (x : Int) : UnitAtom → Prop
  | .nonnegative s r => 0 ≤ s.value * x + rowValue r ν
  | .divisible m s r => ((m + 1 : Nat) : Int) ∣ s.value * x + rowValue r ν
def unitEval (u : UnitFormula) (ν : Nat → Nat) (x : Int) : Prop :=
  match u with
  | .bot => False
  | .top => True
  | .atom a => a.eval ν x
  | .neg p => ¬unitEval p ν x
  | .conj p q => unitEval p ν x ∧ unitEval q ν x
  | .disj p q => unitEval p ν x ∨ unitEval q ν x

def weight (i : Nat) (a : Atom) : Nat :=
  if leading i a.row = 0 then 1 else (leading i a.row).natAbs
def coefficientModulus (i : Nat) (p : Formula) : Nat := ((atoms p).map (weight i)).prod
def nonzeroSign (z : Int) : Sign := if 0 < z then .pos else .neg
def adjustAtom (i M : Nat) : Atom → UnitAtom
  | .nonnegative r =>
    let a := leading i r
    if a = 0 then .nonnegative .zero (remainder i r)
    else .nonnegative (nonzeroSign a) (rowScale ((M / a.natAbs : Nat) : Int) (remainder i r))
  | .divisible m r =>
    let a := leading i r
    if a = 0 then .divisible m .zero (remainder i r)
    else let k := M / a.natAbs
      .divisible ((m + 1) * k - 1) (nonzeroSign a) (rowScale (k : Int) (remainder i r))
def adjust (i M : Nat) : Formula → UnitFormula
  | .truth => .top
  | .falsity => .bot
  | .atom a => .atom (adjustAtom i M a)
  | .negative p => .neg (adjust i M p)
  | .conjunction p q => .conj (adjust i M p) (adjust i M q)
  | .disjunction p q => .disj (adjust i M p) (adjust i M q)

/-- Preserve the actual coefficient-divisibility constraint M | y. -/
def normalize (i : Nat) (p : Formula) : UnitFormula :=
  let M := coefficientModulus i p
  .conj (.atom (.divisible (M - 1) .pos (rowConst 0))) (adjust i M p)
def UnitAtom.period : UnitAtom → Nat
  | .nonnegative _ _ => 1
  | .divisible m _ _ => m + 1
def UnitAtom.cutoffs : UnitAtom → List Row
  | .nonnegative .pos r => [rowScale (-1) r]
  | .nonnegative .neg r => [rowAdd r (rowConst 1)]
  | _ => []
def UnitAtom.instantiate (b : Row) : UnitAtom → Atom
  | .nonnegative s r => .nonnegative (rowAdd (rowScale s.value b) r)
  | .divisible m s r => .divisible m (rowAdd (rowScale s.value b) r)
def period (u : UnitFormula) : Nat := (u.atoms.map UnitAtom.period).prod
def cutoffs (u : UnitFormula) : List Row := rowConst 0 :: u.atoms.flatMap UnitAtom.cutoffs
def instantiate (u : UnitFormula) (b : Row) : Formula :=
  match u with
  | .bot => .falsity
  | .top => .truth
  | .atom a => .atom (a.instantiate b)
  | .neg p => .negative (instantiate p b)
  | .conj p q => .conjunction (instantiate p b) (instantiate q b)
  | .disj p q => .disjunction (instantiate p b) (instantiate q b)

/-- The witness remains a natural, enforced by the actual nonnegative row. -/
def guarded (u : UnitFormula) : UnitFormula :=
  .conj (.atom (.nonnegative .pos (rowConst 0))) u
def unitEliminate (u : UnitFormula) : Formula :=
  BoundedRows.any ((cutoffs u).flatMap (fun b => (List.range (period u)).map
    (fun j => instantiate (guarded u) (rowAdd b (rowConst (j : Int))))))
def eliminate (i : Nat) (p : Formula) : Formula := unitEliminate (normalize i p)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRows
