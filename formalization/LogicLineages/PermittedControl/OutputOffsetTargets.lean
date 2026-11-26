module
public import LogicLineages.PermittedControl.OutputOffsetDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

def ProperEntryRange : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lambda mu : Ordinal.{0}) (t : Nat), lambda<epsilonZero → Order.IsSuccLimit lambda →
  (mu=0 ∨ Order.IsSuccLimit mu) → mu<lambda →
  max 2 (max (actualOrdinalNorm lambda) (actualOrdinalNorm mu))≤t →
  ∃ i n : Nat, 0 < i ∧ FirstEntry f (countInitial lambda t) mu i ∧
    entryNormAt f (countInitial lambda t) i=f^[i] t ∧
    entryNormAt f (countInitial lambda t) i=f n ∧ t≤entryNormAt f (countInitial lambda t) i

def EntryRangeExponentialSeparation : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ U V : Nat, (∃ u, f u=U) → (∃ v, f v=V) → U<V → 2^(U+1)≤V

def SignedOffsetTailEffective : Prop :=
  Primrec (fun p : Nat×Nat => outputOffsetTailCode p.1 p.2) ∧
  (∀ a : Int, ∃ c : Nat, signedOffsetValue c=a) ∧
  ∀ a b : Nat, outputOffsetTailCode a b=(signedOffsetValue a).natAbs+(signedOffsetValue b).natAbs+2

/-- Both strict directions and equality including the exact collision test.
No supplied separation or unbounded-gap assumption. -/
def ActualSignedOffsetComparison : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (U V : Nat) (a b : Int), (∃ u, f u=U) → (∃ v, f v=V) →
  a.natAbs+b.natAbs+2≤min U V →
  (U≠V →
    (((U:Int)+a<(V:Int)+b ↔ U<V) ∧
     ((U:Int)+a≠(V:Int)+b) ∧
     ((V:Int)+b<(U:Int)+a ↔ V<U))) ∧
  (U=V →
    (((U:Int)+a<(V:Int)+b ↔ a<b) ∧
     ((U:Int)+a=(V:Int)+b ↔ a=b) ∧
     ((V:Int)+b<(U:Int)+a ↔ b<a)))

def OutputOffsetFoundation : Prop := ProperEntryRange ∧ EntryRangeExponentialSeparation ∧
  SignedOffsetTailEffective ∧ ActualSignedOffsetComparison

end LogicLineages.PermittedControl.Targets
