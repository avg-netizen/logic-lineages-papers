module
public import LogicLineages.OrdinalComparison.ActualArithmeticCodeDefinitions
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode
open ArithmeticCode

abbrev FreeData := List Nat×List Nat×Nat×Nat
abbrev ActiveData := List Nat×List Nat×Nat×Nat×Nat×Nat×Nat

def leafData (n : Nat) : UnitGroundBlockCode.Payload Nat :=
  (Encodable.decode n).getD (0,0,0,0,0)
def freeData (n : Nat) : FreeData := (Encodable.decode n).getD ([],[],0,0)
def activeData (n : Nat) : ActiveData := (Encodable.decode n).getD ([],[],0,0,0,0,0)
def deleted (i : Nat) (xs : List Nat) := xs.take i ++ xs.drop (i+1)
def shifted (k : Nat) (xs : List Nat) := xs.map (liftCode k)
def positiveVariable (i : Nat) := addCode (variableCode i) (numeralCode 1)

def leafFormula (n : Nat) (xs : List Nat) (r : Nat) : Nat :=
  let b := leafData n
  let inputs := variableCode 2 :: variableCode 1 :: shifted 3 xs
  let factor := b.2.2.2.1
  existsCode (existsCode (existsCode (conjunctionCode [
    observationCode (b.1+2) b.2.1 inputs (variableCode 0),
    observationCode (b.1+2) b.2.2.1 inputs (variableCode 0),
    eqCode (addCode (scaleCode factor (liftCode 3 r)) (positiveVariable 2))
      (addCode (numeralCode (factor*b.2.2.2.2)) (positiveVariable 1)) ])))

def freeFormula (n r child : Nat) : Nat :=
  let d := (freeData n).2.2.2
  existsCode (andCode child (eqCode (positiveVariable 0)
    (addCode (scaleCode (d+1) (liftCode 1 r)) (numeralCode d))))

def activeFormula (n r left right : Nat) : Nat :=
  let m := (activeData n).2.2.2
  let p := m.1
  let d := m.2.1
  let d' := m.2.2.1
  let c := m.2.2.2
  existsCode (existsCode (conjunctionCode [left,right,
    eqCode (addCode (scaleCode (p*d') (positiveVariable 1)) (numeralCode (d*c)))
      (addCode (scaleCode d (positiveVariable 0)) (scaleCode (p*(d'-d)) (liftCode 2 r))) ]))

def unitFormulaCode (n : Nat) (xs : List Nat) (r : Nat) : Nat :=
  if h : n%4=1 ∨ n%4=2 then
    have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
    let p := (n/4).unpair
    have hc : p.2<n := (Nat.unpair_right_le _).trans_lt hd
    if n%4=1 then
      freeFormula p.1 r (unitFormulaCode p.2
        (shifted 1 (deleted (freeData p.1).1.length xs)) (positiveVariable 0))
    else
      have hl : p.2.unpair.1<n := (Nat.unpair_left_le _).trans_lt hc
      have hr : p.2.unpair.2<n := (Nat.unpair_right_le _).trans_lt hc
      let ys := shifted 2 (deleted (activeData p.1).1.length xs)
      activeFormula p.1 r
        (unitFormulaCode p.2.unpair.1 ys (positiveVariable 1))
        (unitFormulaCode p.2.unpair.2 ys (positiveVariable 0))
  else leafFormula (n/4) xs r
termination_by n
decreasing_by all_goals assumption

noncomputable def sourceFormulaCode (Γ : List Nat) (src : Nat) (xs : List Nat) (r : Nat) : Option Nat :=
  (UnitEliminationBuildCode.realizedCompileCode Γ src).map (fun q => unitFormulaCode q xs r)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode
