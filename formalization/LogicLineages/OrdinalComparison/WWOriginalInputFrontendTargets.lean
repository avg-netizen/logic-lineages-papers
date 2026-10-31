module
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalInput ForwardTranslation

def OriginalInputFrontendPrimitiveRecursive : Prop := Primrec frontend

def OriginalInputFrontendArity : Prop :=
  ∀ n : Nat, queryArity (frontend n) = (OriginalInput.decode n).1

def OriginalInputFrontendPointCorrect : Prop :=
  ∀ (n : Nat) (xs : List Nat), codedQueryAt (frontend n) xs = true ↔ Point (OriginalInput.decode n) xs

def OriginalInputFrontendGoodCorrect : Prop :=
  ∀ n : Nat, CodedQueryGood (frontend n) ↔ CodedGood n
end LogicLineages.OrdinalComparison.Source.Targets
