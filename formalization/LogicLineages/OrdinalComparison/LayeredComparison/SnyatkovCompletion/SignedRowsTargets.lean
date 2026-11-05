module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsTargets
open NormalForm SignedRows

def ActualRowTranslation : Prop := ∀ (i j : Nat) (d : Int) (row : Row) (ν : Nat → Nat),
  0 ≤ (ν j : Int) + d →
    rowValue (rowTranslate i j d row) ν = rowValue row (Function.update ν i (replacement j d ν))
def ExactTranslatedOccurrences : Prop := ∀ (i j : Nat) (d : Int) (row : Row),
  (rowTranslate i j d row).2 = row.2.map (fun a => (a.1, translateSummand i j d a.2))
/-- Every original occurrence contributes, independently of its coefficient. -/
def ExactTranslatedDomains : Prop := ∀ (i j : Nat) (d : Int) (row : Row) (ν : Nat → Nat),
  0 ≤ (ν j : Int) + d →
    (rowMeaningful (rowTranslate i j d row) ν ↔
      rowMeaningful row (Function.update ν i (replacement j d ν)))
def ActualCoreTranslation : Prop := ∀ (i j : Nat) (d : Int) (p : Formula) (ν : Nat → Nat),
  0 ≤ (ν j : Int) + d →
    ((core i j d p).eval ν ↔ p.eval (Function.update ν i (replacement j d ν)))
def ExactCoreSupport : Prop := ∀ (i j : Nat) (d : Int) (p : Formula) (v : Nat),
  v ∈ (core i j d p).variables ↔
    (v = j ∧ i ∈ p.variables) ∨ (v ≠ i ∧ v ∈ p.variables)
/-- The outer two-case construction has no nonnegative-anchor premise. -/
def ActualTotalSubstitution : Prop := ∀ (i j : Nat) (d : Int) (p : Formula) (ν : Nat → Nat),
  (substitute i j d p).eval ν ↔ p.eval (Function.update ν i (replacement j d ν))
def ExactTotalSupport : Prop := ∀ (i j : Nat) (d : Int) (p : Formula) (v : Nat),
  v ∈ (substitute i j d p).variables ↔ v = j ∨ (v ≠ i ∧ v ∈ p.variables)
def ActualGuardedAtomTranslation : Prop := ∀ (i j : Nat) (d : Int) (a : Atom) (ν : Nat → Nat),
  (substitute i j d (guardedAtom a)).eval ν ↔
    rowMeaningful a.row (Function.update ν i (replacement j d ν)) ∧
      a.eval (Function.update ν i (replacement j d ν))
def LiteralCodeCalibration : Prop :=
  (∀ (i j : Nat) (d : Int) (s : Summand),
    Code.item i j d s.data = (translateSummand i j d s).data ∧
      Code.offset i d s.data = offset i d s) ∧
  (∀ (i j : Nat) (d : Int) (r : Row), Code.row i j d (rowData r) = rowData (rowTranslate i j d r)) ∧
  (∀ (i j : Nat) (d : Int) (p : Formula), Code.core i j d p.encode = (core i j d p).encode) ∧
  (∀ (i j : Nat) (d : Int) (p : Formula), Code.substitute i j d p.encode = (substitute i j d p).encode)
def ActualNumericPrograms : Prop :=
  Primrec₂ (fun args : Code.Input => Code.item args.1.1 args.1.2 args.2) ∧
  Primrec₂ (fun args : Nat × Int => Code.offset args.1 args.2) ∧
  Primrec₂ (fun args : Code.Input => Code.row args.1.1 args.1.2 args.2) ∧
  Primrec₂ (fun args : Code.Input => Code.core args.1.1 args.1.2 args.2) ∧
  Primrec₂ (fun args : Code.Input => Code.substitute args.1.1 args.1.2 args.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsTargets
