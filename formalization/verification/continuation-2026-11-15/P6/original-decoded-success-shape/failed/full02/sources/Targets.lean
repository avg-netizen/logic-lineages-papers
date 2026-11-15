module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
/-- The five literal active source constructor tags. The original fallback is
inactive for base codes and every unsupported raw tag. -/
def active {alpha : Type} (tag : OTerm alpha) : Formula alpha :=
  eqn tag (numeral 1) ⊔ (eqn tag (numeral 2) ⊔ (eqn tag (numeral 4) ⊔
    (eqn tag (numeral 5) ⊔ eqn tag (numeral 7))))
/-- All raw inputs: success forces matching active constructor tags. Actual
node guard, all field/answer outputs and dispatch witnesses are internal.
This is a necessary-success/non-success theorem, not a claim of output0. -/
def InternalSuccessShape : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node source target sourceTag sourcePayload targetTag targetPayload param : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceTag sourcePayload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetTag targetPayload)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)) →
  Nonempty (Derivation body Delta (eqn sourceTag targetTag ⊓ active sourceTag))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.Targets
