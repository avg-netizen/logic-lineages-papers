module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadArguments.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalConcreteHeadSignature
/-- All six original tags at actual raw pair witnesses, with no decoded-image or
native-calibration premise. The fixed branch AST is exposed internally. -/
def InternalTagFactor : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (tag : Fin 6) (raw payload out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag.val) payload)) →
  (Nonempty (Derivation body Delta (graph1 (arguments n arity) out raw)) ↔
   Nonempty (Derivation body Delta (graph1 (branchArguments n arity tag.val) out payload)))
/-- Ordered application arguments are [domain→result,domain], not a multiset.
The actual payload pair determines the arrow code; actual cons of domain and
nil determines the tail. Neither the output arguments nor signature success
is assumed. Domain/result can be arbitrary arithmetic terms. -/
def InternalApplicationArguments : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw payload domain result tail out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain result)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail domain z)) →
  (Nonempty (Derivation body Delta (graph1 (arguments n arity) out raw)) ↔
   Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out (suc payload) tail)))
/-- Ranked arguments are the literal zero-list recursion at the actual lookup
of the fixed original arity table. Includes malformed/out-of-bound symbols;
head validity remains the separate exact decoder guard of the signature. -/
def InternalRankedArguments : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw symbol count out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) symbol)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup count symbol
    (numeral (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))))) →
  (Nonempty (Derivation body Delta (graph1 (arguments n arity) out raw)) ↔
   Nonempty (Derivation body Delta (graph1 groundList out count)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadArguments.Targets
