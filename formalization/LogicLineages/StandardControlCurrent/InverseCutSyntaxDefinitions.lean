module
public import LogicLineages.StandardControlCurrent.InverseCutDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ContractDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCutSyntax
open OrdinalComparison LayeredComparison.SnyatkovCompletion
-- h=0 selects Phi; every nonzero h selects the actual fixed-seed H.
def function (h : Nat) : Nat → Nat := if h = 0 then Phi else FixedSeedControlResidue.H
def apply (h : Nat) (t : Term) : Term := if h = 0 then .phi t else .hyper t
def inverse (h : Nat) (t : Term) : Term := if h = 0 then .phiInverse t else .hyperInverse t
def le (a b : Term) : Matrix := .negative (.less b a)
def remainder (m : Nat) (a : Term) : Term := .subtract a (.multiply m (.divide m a))
def next (m r : Nat) (a : Term) : Term :=
  .add a (remainder m (.subtract (.numeral (r+m)) (remainder m a)))
def branch (h m r : Nat) (a b hi lower : Term) : Matrix :=
  .disjunction
    (.conjunction (le lower a)
      (.conjunction (le (next m r a) b) (le (apply h (next m r a)) hi)))
    (.conjunction (.less a lower)
      (.conjunction (le (next m r lower) b) (le (apply h (next m r lower)) hi)))
def compile (h m r : Nat) (a b lo hi : Term) : Matrix :=
  if 0 < m ∧ r < m then
    .disjunction
      (.conjunction (le lo (apply h (.numeral 0))) (branch h m r a b hi (.numeral 0)))
      (.conjunction (.less (apply h (.numeral 0)) lo)
        (branch h m r a b hi (.add (inverse h (.subtract lo (.numeral 1))) (.numeral 1))))
  else .falsity

def support (a b lo hi : Term) : List Nat := a.variables ++ b.variables ++ lo.variables ++ hi.variables

def BoundCut (h m r x : Nat) (a b lo hi : Term) (ν : Nat → Nat) : Prop :=
  0 < m ∧ r < m ∧ ∃ n : Nat,
    let ρ := Function.update ν x n
    a.value ρ ≤ ρ x ∧ ρ x ≤ b.value ρ ∧
    lo.value ρ ≤ function h (ρ x) ∧ function h (ρ x) ≤ hi.value ρ ∧ ρ x % m = r

-- Raw constructor program operates on arbitrary input codes without a decoder oracle.
def numeralCode (n : Nat) := 10*n
def addCode (a b : Nat) := 10*Nat.pair a b+2
def subCode (a b : Nat) := 10*Nat.pair a b+3
def mulCode (m a : Nat) := 10*Nat.pair m a+4
def divCode (m a : Nat) := 10*Nat.pair m a+5
def applyCode (h a : Nat) := 10*a+(if h = 0 then 6 else 7)
def inverseCode (h a : Nat) := 10*a+(if h = 0 then 8 else 9)
def lessCode (a b : Nat) := 8*Nat.pair a b+3
def negCode (p : Nat) := 8*p+5
def andCode (p q : Nat) := 8*Nat.pair p q+6
def orCode (p q : Nat) := 8*Nat.pair p q+7
def leCode (a b : Nat) := negCode (lessCode b a)
def remainderCode (m a : Nat) := subCode a (mulCode m (divCode m a))
def nextCode (m r a : Nat) := addCode a (remainderCode m (subCode (numeralCode (r+m)) (remainderCode m a)))
def branchCode (h m r a b hi lower : Nat) :=
  orCode
    (andCode (leCode lower a) (andCode (leCode (nextCode m r a) b) (leCode (applyCode h (nextCode m r a)) hi)))
    (andCode (lessCode a lower) (andCode (leCode (nextCode m r lower) b) (leCode (applyCode h (nextCode m r lower)) hi)))
def compileCode (h m r a b lo hi : Nat) :=
  if 0 < m ∧ r < m then
    orCode
      (andCode (leCode lo (applyCode h (numeralCode 0))) (branchCode h m r a b hi (numeralCode 0)))
      (andCode (lessCode (applyCode h (numeralCode 0)) lo)
        (branchCode h m r a b hi (addCode (inverseCode h (subCode lo (numeralCode 1))) (numeralCode 1))))
  else 1
abbrev Input := Nat × Nat × Nat × Nat × Nat × Nat × Nat
def program (p : Input) : Nat := compileCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2
end LogicLineages.StandardControlCurrent.InverseCutSyntax
