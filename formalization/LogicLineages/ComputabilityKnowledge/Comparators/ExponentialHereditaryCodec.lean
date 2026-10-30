module

public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodec

@[expose] public section

/-! Full faithful hereditary finite-code representation supplier.
The denotation is the existing actual finite-map model, not a new value-only
surrogate. Canonicalization is an explicitly defined natural-number operation
with a genuine uniform primitive-recursive obligation. Coverage is existential
for mathematical forms; it is not computable extraction from a classical map.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialHereditaryCodec

open ExponentialNormalForm
open LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodec

def Canonicalization : Prop :=
  ∀ (d h n : Nat),
    CodeCanonical d h (canonicalize d h n) ∧
    formDecode d h (canonicalize d h n) = formDecode d h n

def Faithfulness : Prop :=
  ∀ (d h n m : Nat),
    CodeCanonical d h n → CodeCanonical d h m →
    (formDecode d h n = formDecode d h m ↔ n = m)

def FixedPoints : Prop :=
  ∀ (d h n : Nat), CodeCanonical d h n → canonicalize d h n = n

def Coverage : Prop :=
  ∀ (d h : Nat) (f : Form d h),
    ∃ n : Nat, CodeCanonical d h n ∧ formDecode d h n = f

def ZeroAndConstants : Prop :=
  ∀ (d h n : Nat),
    CodeCanonical d h (zeroCode d h) ∧
    formDecode d h (zeroCode d h) = zeroForm h ∧
    CodeCanonical d h (constantCode d h n) ∧
    formDecode d h (constantCode d h n) = constantForm h n

def ActualPrimitiveRecursion : Prop :=
  Primrec (fun p : Nat × Nat × Nat => canonicalize p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat => zeroCode p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × Nat => constantCode p.1 p.2.1 p.2.2)

def Target : Prop := Canonicalization ∧ Faithfulness ∧ FixedPoints ∧
  Coverage ∧ ZeroAndConstants ∧ ActualPrimitiveRecursion

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialHereditaryCodec
