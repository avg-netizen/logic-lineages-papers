module
public import LogicLineages.OrdinalComparison.OrdinalSyntaxPrimitiveFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntaxPrimitiveFold.Targets

def ExactRawRecursion : Prop := OrdinalSyntaxComputableFold.Targets.ExactRawRecursion

def IndexedPrimitiveRecursive : Prop := ∀ (P A : Type) [Primcodable P] [Primcodable A]
    (leaf : P × Nat → A) (branch : P × (Nat × A × A) → A),
  Primrec leaf → Primrec branch →
    Primrec (fun p : P × Nat => OrdinalSyntaxComputableFold.indexedFold leaf branch p.1 p.2)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntaxPrimitiveFold.Targets
