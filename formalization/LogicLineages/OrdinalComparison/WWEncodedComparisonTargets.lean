module
public import LogicLineages.OrdinalComparison.WWEncodedComparisonDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

def PositiveComparisonPrimitiveRecursive : Prop := Primrec₂ positiveComparison

def PositiveComparisonSourceCorrect : Prop :=
  ∀ a b : List NONote, positiveComparison (normalCodes a) (normalCodes b) = true ↔
    ∀ j : Nat, positiveNoteAt a j ≤ positiveNoteAt b j

def EncodedQueryAtComputable : Prop :=
  Computable (fun p : EncodedQuery × List Nat => encodedQueryAt p.1 p.2)

def EncodedQueryAtSourceCorrect : Prop :=
  ∀ (ι : Type) (index : ι → Nat) (strict : Bool) (a b : Scalar ι)
    (ap bp : List NONote) (xs : List Nat),
    encodedQueryAt (strict, (scalarCode index a, normalCodes ap),
      (scalarCode index b, normalCodes bp)) xs = true ↔
      (∀ j, positiveNoteAt ap j ≤ positiveNoteAt bp j) ∧
      (if strict then a.value (fun i => xs.getD (index i) 0 + 1) < b.value (fun i => xs.getD (index i) 0 + 1)
       else a.value (fun i => xs.getD (index i) 0 + 1) ≤ b.value (fun i => xs.getD (index i) 0 + 1))
end LogicLineages.OrdinalComparison.Source.Targets
