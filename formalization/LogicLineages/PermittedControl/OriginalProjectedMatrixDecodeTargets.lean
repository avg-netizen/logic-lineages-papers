module
public import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableTargets
public import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalProjectedMatrixDecode
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PreparedInput)
open MixedSameRankResidue (WeightedOperand)
open HeterogeneousSignedMatrixSlice (Row)
open SignedRowGuardedTest (Test)

abbrev Summand := Int × NormalForm.Summand

def decodeTerm (ops : List LowerOperand) (t : Summand) : Option WeightedOperand :=
  match t.2 with
  | .variable 0 => none
  | .variable (j+1) => ops[j]?.map (fun op => (t.1,op))
  | _ => none

def decodeTerms (ops : List LowerOperand) : List Summand → Option (List WeightedOperand)
  | [] => some []
  | t :: ts => do
      let term ← decodeTerm ops t
      let rest ← decodeTerms ops ts
      pure (term :: rest)

def testOf : NormalForm.Atom → Test
  | .nonnegative _ => .nonnegative
  | .divisible m _ => .congruence (m+1)

def decodeAtom (ops : List LowerOperand) (a : NormalForm.Atom) : Option Row :=
  (decodeTerms ops a.row.2).map (fun ts => (testOf a,a.row.1,ts))

def decodeAtoms (ops : List LowerOperand) : List NormalForm.Atom → Option (List Row)
  | [] => some []
  | a :: atoms => do
      let row ← decodeAtom ops a
      let rest ← decodeAtoms ops atoms
      pure (row :: rest)

def decode (ops : List LowerOperand) (p : NormalForm.Formula) : Option (List Row) :=
  decodeAtoms ops (LinearRows.atoms p)

def FitsOutput (ops : List LowerOperand) (p : NormalForm.Formula) : Prop :=
  PreparedInput ops p ∧ ∀ n ∈ p.variables, 0 < n

def LiteralTerm (ops : List LowerOperand) (t : Summand) (out : WeightedOperand) : Prop :=
  ∃ j : Nat, ∃ h : j < ops.length,
    t.2 = .variable (j+1) ∧ out = (t.1,ops[j])

def LiteralRow (ops : List LowerOperand) (a : NormalForm.Atom) (row : Row) : Prop :=
  row.1 = testOf a ∧ row.2.1 = a.row.1 ∧ List.Forall₂ (LiteralTerm ops) a.row.2 row.2.2

def ExactProjectedMatrixDecode : Prop :=
  (∀ (ops : List LowerOperand) (t : Summand) (o : WeightedOperand),
    decodeTerm ops t = some o ↔ LiteralTerm ops t o) ∧
  (∀ (ops : List LowerOperand) (p : NormalForm.Formula) (rows : List Row),
    decode ops p = some rows ↔ List.Forall₂ (LiteralRow ops) (LinearRows.atoms p) rows) ∧
  ∀ (ops : List LowerOperand) (p : NormalForm.Formula), FitsOutput ops p →
    ∃ rows : List Row, decode ops p = some rows

end LogicLineages.PermittedControl.OriginalProjectedMatrixDecode
