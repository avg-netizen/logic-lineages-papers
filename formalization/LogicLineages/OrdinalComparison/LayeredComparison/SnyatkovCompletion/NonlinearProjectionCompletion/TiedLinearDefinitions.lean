module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions
public import Mathlib.Data.List.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinear
open BlockRows

deriving instance DecidableEq for Term
deriving instance DecidableEq for NormalForm.Summand

/-- A parameter term and an occurrence have different roles. Other bound
names' nonlinear occurrences must remain in the occurrence list after QE. -/
inductive Token where
  | parameter (term : Term)
  | occurrence (summand : NormalForm.Summand)
  deriving DecidableEq

def Token.value (ν : Nat → Nat) : Token → Nat
  | .parameter t => t.value ν
  | .occurrence s => s.term.value ν
def rowTokens (r : Row) : List Token :=
  [.parameter r.1.1, .parameter r.1.2] ++ r.2.map (fun a => .occurrence a.2)
def tokens : Formula → List Token
  | .truth | .falsity => []
  | .atom a => rowTokens a.row
  | .negative p => tokens p
  | .conjunction p q | .disjunction p q => tokens p ++ tokens q

def rawToken (x : Nat) : Token := .occurrence (.variable x)
def tokenName (table : List Token) (x : Nat) (t : Token) : Nat :=
  if t = rawToken x then 0 else table.idxOf t + 1
def tokenOfName (table : List Token) (x j : Nat) : Token :=
  if j = 0 then rawToken x else table[j - 1]?.getD (.parameter (.numeral 0))

/-- This ONE valuation precedes the sole Cooper witness. No parameter token
is existentially quantified, even when several tokens have equal values. -/
def parameterValuation (table : List Token) (x : Nat) (ν : Nat → Nat) (j : Nat) : Nat :=
  (tokenOfName table x j).value ν

def liftRow (table : List Token) (x : Nat) (r : Row) : NormalForm.Row :=
  (0, (1, .variable (tokenName table x (.parameter r.1.1))) ::
    (-1, .variable (tokenName table x (.parameter r.1.2))) ::
    r.2.map (fun a => (a.1, .variable (tokenName table x (.occurrence a.2)))))
def liftAtom (table : List Token) (x : Nat) : Atom → NormalForm.Atom
  | .nonnegative r => .nonnegative (liftRow table x r)
  | .divisible m r => .divisible m (liftRow table x r)
def liftFormula (table : List Token) (x : Nat) : Formula → NormalForm.Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (liftAtom table x a)
  | .negative p => .negative (liftFormula table x p)
  | .conjunction p q => .conjunction (liftFormula table x p) (liftFormula table x q)
  | .disjunction p q => .disjunction (liftFormula table x p) (liftFormula table x q)

def lowerSummand (table : List Token) (x : Nat) : NormalForm.Summand → Token
  | .variable j => tokenOfName table x j
  | .phi _ _ | .hyperPhi _ _ _ => .parameter (.numeral 0)

/-- Literal lowering, with signed parameter coefficients held in the two
expanded constants and source occurrences kept in their original role. -/
def lowerEntries (table : List Token) (x : Nat) (positive negative : Term) :
    List (Int × NormalForm.Summand) → Row
  | [] => ((positive, negative), [])
  | a :: entries =>
      let r := lowerEntries table x positive negative entries
      match lowerSummand table x a.2 with
      | .parameter t =>
          ((.add (.multiply a.1.toNat t) r.1.1,
            .add (.multiply (-a.1).toNat t) r.1.2), r.2)
      | .occurrence s => (r.1, (a.1, s) :: r.2)
def lowerRow (table : List Token) (x : Nat) (r : NormalForm.Row) : Row :=
  lowerEntries table x (.numeral r.1.toNat) (.numeral (-r.1).toNat) r.2
def lowerAtom (table : List Token) (x : Nat) : NormalForm.Atom → Atom
  | .nonnegative r => .nonnegative (lowerRow table x r)
  | .divisible m r => .divisible m (lowerRow table x r)
def lowerFormula (table : List Token) (x : Nat) : NormalForm.Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (lowerAtom table x a)
  | .negative p => .negative (lowerFormula table x p)
  | .conjunction p q => .conjunction (lowerFormula table x p) (lowerFormula table x q)
  | .disjunction p q => .disjunction (lowerFormula table x p) (lowerFormula table x q)

/-- The SAME existing natural-witness Cooper kernel used by the accepted
word adapter. This is a concrete compiler, not an elimination supplier field. -/
def eliminate (x : Nat) (p : Formula) : Formula :=
  let table := tokens p
  lowerFormula table x (LinearRows.eliminate 0 (liftFormula table x p))

def allowed (bound : List Nat) : Formula → Bool
  | .truth | .falsity => true
  | .atom a => PlainMaximum.allowed bound a.row
  | .negative p => allowed bound p
  | .conjunction p q | .disjunction p q => allowed bound p && allowed bound q

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinear
