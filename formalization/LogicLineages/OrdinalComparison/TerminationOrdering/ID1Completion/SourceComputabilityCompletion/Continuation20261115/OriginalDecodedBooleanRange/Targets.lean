module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
/-- Every actual standalone exchange output is Boolean on ALL raw inputs.
No validity, constructor, recursive-answer range, native-image or guard premise.
The option-layer output is one greater and is not confused with this payload. -/
def InternalExchangeRange : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node param out : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 (OriginalDecodedExchangeEquation.exchange n arity) out node param)) →
  Nonempty (Derivation body Delta (eqn out (numeral 0) ⊔ eqn out (numeral 1)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.Targets
