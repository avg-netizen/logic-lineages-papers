module
public import LogicLineages.PermittedControl.InverseTableDefinitions
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Complete semantic unequal-gap table with the actual constructed partner,
cocycle, both brackets and all comparison/equality iff rows. No hits, partner
ordering, residue or comparison signs are supplied as hypotheses. -/
def ActualInverseTable : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lambda mu nu delta : NONote), Order.IsSuccLimit lambda.1.repr →
  (mu.1.repr=0 ∨ Order.IsSuccLimit mu.1.repr) →
  (nu.1.repr=0 ∨ Order.IsSuccLimit nu.1.repr) → Order.IsSuccLimit delta.1.repr →
  mu.1.repr < lambda.1.repr → delta.1.repr < lambda.1.repr-mu.1.repr →
  ∀ x y : Nat, inverseTableTail lambda mu nu delta B ≤ x →
  inverseTableTail lambda mu nu delta B ≤ y →
  let kappa := mu.1.repr+delta.1.repr
  let lambdaQ := nu.1.repr+delta.1.repr
  let A := countInitial lambda.1.repr x
  let Q := countInitial lambdaQ y
  let sign := equalGapCertificateCode (rawNoteEncode mu.1) (rawNoteEncode nu.1)
    (rawNoteEncode delta.1)
  mu.1.repr < kappa ∧ kappa < lambda.1.repr ∧
  ∃ i j p q lo mid hi : Nat,
    FirstEntry f A kappa i ∧
    let h := entryNormAt f A i
    x ≤ h ∧ 0<h ∧
    FirstEntry f (countInitial kappa h) mu.1.repr j ∧
    FirstEntry f A mu.1.repr p ∧ FirstEntry f Q nu.1.repr q ∧ p=i+j ∧
    entryNormAt f A p=entryNormAt f (countInitial kappa h) j ∧
    FirstEntry f (countInitial lambdaQ (h-1)) nu.1.repr lo ∧
    FirstEntry f (countInitial lambdaQ h) nu.1.repr mid ∧
    FirstEntry f (countInitial lambdaQ (h+1)) nu.1.repr hi ∧
    entryNormAt f (countInitial lambdaQ (h-1)) lo < entryNormAt f A p ∧
    entryNormAt f A p < entryNormAt f (countInitial lambdaQ (h+1)) hi ∧
    numericalComparison (entryNormAt f A p) (entryNormAt f (countInitial lambdaQ h) mid)=sign ∧
    InverseTableRows sign y h (entryNormAt f Q q) (entryNormAt f A p) ∧
    (mu.1.repr=0 → nu.1.repr=0 → kappa=lambdaQ ∧ sign=1)

end LogicLineages.PermittedControl.Targets
