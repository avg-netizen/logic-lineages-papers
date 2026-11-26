module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261116.OriginalConcreteHeadSignature
/-- Complete application-head signature equation at actual constructor data.
The original decoder success is DERIVED, not an additional premise. -/
def InternalApplicationSignature : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw payload domain result tail args packed out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain result)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail domain z)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode args (suc payload) tail)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed result args)) →
  (Nonempty (Derivation body Delta (graph1 (signature n arity) out raw)) ↔
   Nonempty (Derivation body Delta (eqn out (suc packed))))
/-- Complete ranked-head signature equation. The only validity premise is the
original finite symbol bound. Actual lookup/recursion/packing witnesses specify
the source argument list, and no signature or decoder-success oracle is assumed. -/
def InternalRankedSignature : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw symbol count args packed out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) symbol)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess symbol (numeral n))) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup count symbol
    (numeral (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))))) →
  Nonempty (Derivation body Delta (graph1 groundList args count)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed z args)) →
  (Nonempty (Derivation body Delta (graph1 (signature n arity) out raw)) ↔
   Nonempty (Derivation body Delta (eqn out (suc packed))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.Targets
