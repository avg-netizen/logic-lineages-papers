module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode
open SignedPair

def variableCode (i : Nat) : Nat := 6 * i + 1
def addCode (a b : Nat) : Nat := 6 * Nat.pair a b + 2
def negateCode (a : Nat) : Nat := 6 * a + 3
def shiftCode (a : Nat) : Nat := 6 * a + 4
def zeroCode : Nat := addCode 0 (negateCode 0)
def repeatCode (a k : Nat) : Nat := ((addCode a)^[k]) zeroCode

/-- Literal repeated shift/addition expansion, including zero and negative
coefficients. The optional unknown is an original shared source index. -/
def expandMonomial (m : MonomialCode) : Nat :=
  let base := match m.2.2 with | none => 0 | some i => variableCode i
  let body := repeatCode ((shiftCode^[m.2.1]) base) m.1.natAbs
  if m.1 < 0 then negateCode body else body

def validMonomial (n : Nat) (m : MonomialCode) : Bool :=
  match m.2.2 with | none => true | some i => decide (i < n)
def monomialCode (n : Nat) (m : MonomialCode) : Option Nat :=
  if validMonomial n m then some (expandMonomial m) else none

def rowCode (n : Nat) (row : List MonomialCode) : Nat :=
  row.foldr (fun m a => match monomialCode n m with
    | none => a | some b => addCode b a) zeroCode

/-- The one original dimension n is also the one closed seed index. Every
variable occurrence gets the SAME substitution, including repeated rows. -/
def subtractSeedCode (n : Nat) : Nat → Nat
  | e =>
    if e % 6 = 1 then addCode (variableCode (e / 6)) (negateCode (variableCode n))
    else if h : e % 6 = 2 ∨ e % 6 = 3 ∨ e % 6 = 4 then
      have hd : e / 6 < e := Nat.div_lt_self (by omega) (by decide)
      if e % 6 = 2 then
        have hl : (e / 6).unpair.1 < e := (Nat.unpair_left_le _).trans_lt hd
        have hr : (e / 6).unpair.2 < e := (Nat.unpair_right_le _).trans_lt hd
        addCode (subtractSeedCode n (e / 6).unpair.1)
          (subtractSeedCode n (e / 6).unpair.2)
      else if e % 6 = 3 then negateCode (subtractSeedCode n (e / 6))
      else shiftCode (subtractSeedCode n (e / 6))
    else 0
termination_by e => e
decreasing_by all_goals assumption

def inputCode (c : SystemCode) : List Nat := c.2.map (rowCode c.1)
def seededInputCode (c : SystemCode) : List Nat :=
  (inputCode c).map (subtractSeedCode c.1)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode
