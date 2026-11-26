module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)
def NativeLookup : Prop := ∀ (entries : List (Nat × Nat)) (key : Nat),
  evaluate lookup (List.Vector.ofFn ![numbersNumber (entries.map (fun p => Nat.pair p.1 p.2)),key]) =
    Encodable.encode (entries.lookup key)
def NativeMapGraph : Prop := ∀ (entries : List (Nat × Nat)) (keys : List Nat),
  evaluate mapGraph (List.Vector.ofFn ![numbersNumber keys,
    numbersNumber (entries.map (fun p => Nat.pair p.1 p.2))]) =
    numbersNumber (keys.flatMap (fun key => (entries.lookup key).toList))
def InternalFirstHit : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (code entry tail key value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code entry tail)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry key value)) →
  Nonempty (Derivation body Delta (graph2 lookup (suc value) code key))
def InternalMissTail : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (code entry tail entryKey value key out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code entry tail)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry entryKey value)) →
  Nonempty (Derivation body Delta (eqn entryKey key).not) →
  (Nonempty (Derivation body Delta (graph2 lookup out code key)) ↔
   Nonempty (Derivation body Delta (graph2 lookup out tail key)))
/-- Exact omission behavior for a missing lookup, without assuming graph completeness. -/
def InternalMapMissing : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (keys key tail entries out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys key tail)) →
  Nonempty (Derivation body Delta (graph2 lookup (InternalTagArithmeticSyntaxProof.z) entries key)) →
  (Nonempty (Derivation body Delta (graph2 mapGraph out keys entries)) ↔
   Nonempty (Derivation body Delta (graph2 mapGraph out tail entries)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.Targets
