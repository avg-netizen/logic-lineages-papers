module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)
def NativeGraph : Prop := ∀ (R D : Program 2) (G : Program 3)
    (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (g : Nat → List Nat → Nat → Option Nat),
  (∀ seed param, evaluate R (List.Vector.ofFn ![seed,param]) = m seed param) →
  (∀ node param, evaluate D (List.Vector.ofFn ![node,param]) = numbersNumber (d node param)) →
  (∀ node vals param, evaluate G (List.Vector.ofFn ![node,numbersNumber vals,param]) =
    Encodable.encode (g node vals param)) →
  ∀ (i seed param : Nat), evaluate (graph R D G) (List.Vector.ofFn ![i,seed,param]) =
    numbersNumber ((graphList m d g seed param i).map (fun kv => Nat.pair kv.1 kv.2))
/-- Exact native table coherence under the actual rank-decrease and layer laws.
These are explicit native assumptions; no internal correctness follows by reflection. -/
def NativeCoherentGraph : Prop := ∀ (R D : Program 2) (G : Program 3)
    (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (g : Nat → List Nat → Nat → Option Nat) (f : Nat → Nat → Nat),
  (∀ seed param, evaluate R (List.Vector.ofFn ![seed,param]) = m seed param) →
  (∀ node param, evaluate D (List.Vector.ofFn ![node,param]) = numbersNumber (d node param)) →
  (∀ node vals param, evaluate G (List.Vector.ofFn ![node,numbersNumber vals,param]) =
    Encodable.encode (g node vals param)) →
  (∀ node param child, child ∈ d node param → m child param < m node param) →
  (∀ node param, g node ((d node param).map (fun child => f child param)) param = some (f node param)) →
  ∀ (i seed param : Nat), i ≤ m seed param + 1 →
    evaluate (graph R D G) (List.Vector.ofFn ![i,seed,param]) =
      numbersNumber ((frontierList d seed param (m seed param + 1 - i)).map
        (fun node => Nat.pair node (f node param)))
def InternalZero : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (R D : Program 2) (G : Program 3) (seed param : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (graph R D G) z z seed param))
def InternalSuccessor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (R D : Program 2) (G : Program 3)
    (i seed param old rankValue depth nodes out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (graph R D G) old i seed param)) →
  Nonempty (Derivation body Delta (graph2 R rankValue seed param)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth i rankValue)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) nodes depth seed param)) →
  (Nonempty (Derivation body Delta (graph3 (graph R D G) out (suc i) seed param)) ↔
   Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out nodes old param)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.Targets
