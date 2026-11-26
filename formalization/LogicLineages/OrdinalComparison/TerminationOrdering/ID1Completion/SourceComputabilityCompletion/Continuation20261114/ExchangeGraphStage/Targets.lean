module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)
/-- Coverage is explicit: omitting absent keys cannot silently become total mapping. -/
def NativeCoveredMap : Prop := ∀ (keys carrier : List Nat) (f : Nat → Nat),
  (∀ k ∈ keys, k ∈ carrier) →
  evaluate ExchangeMapGraph.mapGraph (List.Vector.ofFn ![numbersNumber keys,
    numbersNumber (carrier.map (fun k => Nat.pair k (f k)))]) =
    numbersNumber (keys.map f)
def NativeStage : Prop := ∀ (D : Program 2) (G : Program 3)
    (d : Nat → Nat → List Nat) (g : Nat → List Nat → Nat → Option Nat),
  (∀ node param, evaluate D (List.Vector.ofFn ![node,param]) = numbersNumber (d node param)) →
  (∀ node vals param, evaluate G (List.Vector.ofFn ![node,numbersNumber vals,param]) =
    Encodable.encode (g node vals param)) →
  ∀ (frontier : List Nat) (old : List (Nat × Nat)) (param : Nat),
    evaluate (stage D G) (List.Vector.ofFn ![numbersNumber frontier,
      numbersNumber (old.map (fun kv => Nat.pair kv.1 kv.2)),param]) =
    numbersNumber ((frontier.filterMap (fun node =>
      (g node ((d node param).flatMap (fun k => (old.lookup k).toList)) param).map
        (fun value => Nat.pair node value))))
def InternalSkip : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2) (G : Program 3)
    (frontier node tail old param deps vals out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph vals deps old)) →
  Nonempty (Derivation body Delta (graph3 G z node vals param)) →
  (Nonempty (Derivation body Delta (graph3 (stage D G) out frontier old param)) ↔
   Nonempty (Derivation body Delta (graph3 (stage D G) out tail old param)))
def InternalKeep : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2) (G : Program 3)
    (frontier node tail old param deps vals value pair rest out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph vals deps old)) →
  Nonempty (Derivation body Delta (graph3 G (suc value) node vals param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)) →
  Nonempty (Derivation body Delta (graph3 (stage D G) rest tail old param)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair rest)) →
  Nonempty (Derivation body Delta (graph3 (stage D G) out frontier old param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.Targets
