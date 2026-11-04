module
public import LogicLineages.OrdinalComparison.OrdinalSyntaxComputableFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntaxComputableFold.Targets

def ExactRawRecursion : Prop :=
  (∀ n : Nat, ¬atom n → (n/8).unpair.1<n ∧ (n/8).unpair.2<n) ∧
  ∀ (P A : Type) (leaf : P × Nat → A) (branch : P × (Nat × A × A) → A) (p : P) (n : Nat),
    indexedFold leaf branch p n = if atom n then leaf (p,n) else
      branch (p,n%8,indexedFold leaf branch p (n/8).unpair.1,
        indexedFold leaf branch p (n/8).unpair.2)

def IndexedComputable : Prop := ∀ (P A : Type) [Primcodable P] [Primcodable A]
    (leaf : P × Nat → A) (branch : P × (Nat × A × A) → A),
  Computable leaf → Computable branch →
    Computable (fun p : P × Nat => indexedFold leaf branch p.1 p.2)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntaxComputableFold.Targets
