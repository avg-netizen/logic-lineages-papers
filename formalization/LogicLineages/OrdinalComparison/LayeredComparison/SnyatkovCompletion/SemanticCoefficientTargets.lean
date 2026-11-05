module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientTargets
open SemanticCoefficient Source.ForwardTranslation

/-- Sound and COMPLETE for the actual original closed coefficient ordinal,
not merely for an Omega-free syntactic subclass. -/
def ExactNaturalValue : Prop := ∀ (c : ClosedPositive) (k : Nat),
  Code.recognize (closedPositiveCode c) = some k ↔ c.evaluate.1.repr = (k : Ordinal.{0})

def ExactFiniteAcceptance : Prop := ∀ c : ClosedPositive,
  (∃ k, Code.recognize (closedPositiveCode c) = some k) ↔ c.evaluate.1.repr < Ordinal.omega0

def ExactNonfiniteRejection : Prop := ∀ c : ClosedPositive,
  Code.recognize (closedPositiveCode c) = none ↔ Ordinal.omega0 ≤ c.evaluate.1.repr

def PositiveOutput : Prop := ∀ (c : ClosedPositive) k,
  Code.recognize (closedPositiveCode c) = some k → 0 < k

/-- The accepted structural compiler's positive results are retained exactly.
No equality with its rejection set, nor new vector-consumer scope, is assumed. -/
def StructuralExtension : Prop := ∀ (c : ClosedPositive) k,
  FiniteCoefficientBase.coefficient c = some k → Code.recognize (closedPositiveCode c) = some k

def ActualNumericProgram : Prop := Primrec Code.recognize
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientTargets
