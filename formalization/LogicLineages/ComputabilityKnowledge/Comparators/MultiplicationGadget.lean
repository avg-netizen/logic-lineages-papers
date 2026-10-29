module

public import LogicLineages.ComputabilityKnowledge.PositiveExpression

@[expose] public section

/-!
# Independent statement of the seven-equation multiplication gadget

Paper02, `lem:seven-equations`, with the exact positive domain, affine a,b,
and all eight positive witnesses. The numerical source equations, their literal expression syntax and their
depth bound are specified separately and must all be proved by a candidate.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.MultiplicationGadget

open PositiveExpression

def firstAffine (x y : PosNat) : Nat := x.val + y.val + 1

def secondAffine (x y : PosNat) : Nat := firstAffine x y + x.val

def SevenEquations (x y w s t u v q r h k : PosNat) : Prop :=
  let a := firstAffine x y
  let b := secondAffine x y
  (2 ^ a * u.val + 1 = u.val + 2 ^ s.val) ∧
  (2 ^ b * v.val + 1 = v.val + 2 ^ t.val) ∧
  (2 ^ a * q.val + y.val + 1 = u.val + q.val + 2 ^ a) ∧
  (2 ^ b * r.val + y.val + 1 = v.val + r.val + 2 ^ b) ∧
  (s.val + a + h.val = 2 ^ a * a) ∧
  (t.val + b + k.val = 2 ^ b * b) ∧
  (t.val = s.val + w.val)

def NumericalTarget : Prop :=
  ∀ x y w : PosNat,
    w.val = x.val * y.val ↔
      ∃ s t u v q r h k : PosNat, SevenEquations x y w s t u v q r h k

/-- Exactly the three inputs and eight fresh auxiliary names. -/
inductive Variable where
  | x | y | w | s | t | u | v | q | r | h | k
  deriving DecidableEq

def valuation (x y w s t u v q r h k : PosNat) : Variable → PosNat
  | .x => x
  | .y => y
  | .w => w
  | .s => s
  | .t => t
  | .u => u
  | .v => v
  | .q => q
  | .r => r
  | .h => h
  | .k => k

def aTerm : Expr Variable := .add (.add (.var .x) (.var .y)) .one

def bTerm : Expr Variable := .add aTerm (.var .x)

/-- The literal seven displayed pairs of source expressions, in paper order. -/
def equations : List (Expr Variable × Expr Variable) :=
  [(.add (.emul aTerm (.var .u)) .one,
      .add (.var .u) (.emul (.var .s) .one)),
   (.add (.emul bTerm (.var .v)) .one,
      .add (.var .v) (.emul (.var .t) .one)),
   (.add (.add (.emul aTerm (.var .q)) (.var .y)) .one,
      .add (.add (.var .u) (.var .q)) (.emul aTerm .one)),
   (.add (.add (.emul bTerm (.var .r)) (.var .y)) .one,
      .add (.add (.var .v) (.var .r)) (.emul bTerm .one)),
   (.add (.add (.var .s) aTerm) (.var .h), .emul aTerm aTerm),
   (.add (.add (.var .t) bTerm) (.var .k), .emul bTerm bTerm),
   (.var .t, .add (.var .s) (.var .w))]

def SourceEquations (ρ : Variable → PosNat) : Prop :=
  ∀ pair ∈ equations, pair.1.eval ρ = pair.2.eval ρ

def SourceCorrespondence : Prop :=
  ∀ x y w s t u v q r h k : PosNat,
    SourceEquations (valuation x y w s t u v q r h k) ↔
      SevenEquations x y w s t u v q r h k

def SourceDepth : Prop :=
  ∀ pair ∈ equations, pair.1.depth ≤ 1 ∧ pair.2.depth ≤ 1

/-- Full local lemma: numerical equivalence, literal syntax, and stated depth. -/
def Target : Prop := NumericalTarget ∧ SourceCorrespondence ∧ SourceDepth

end LogicLineages.ComputabilityKnowledge.Comparators.MultiplicationGadget
