module
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

def EncodedClosedPositiveCorrect : Prop :=
  ∀ c : ClosedPositive, encodedClosedPositive (closedPositiveCode c) = rawNoteEncode c.evaluate.1

def EncodedClosedPositivePrimitiveRecursive : Prop := Primrec encodedClosedPositive

def EncodedClosedHeadCorrect : Prop :=
  ∀ c : ClosedPositive, encodedClosedHead (closedPositiveCode c) = rawNoteEncode (scalarHeadNote c).1

def EncodedClosedHeadPrimitiveRecursive : Prop := Primrec encodedClosedHead
end LogicLineages.OrdinalComparison.Source.Targets
