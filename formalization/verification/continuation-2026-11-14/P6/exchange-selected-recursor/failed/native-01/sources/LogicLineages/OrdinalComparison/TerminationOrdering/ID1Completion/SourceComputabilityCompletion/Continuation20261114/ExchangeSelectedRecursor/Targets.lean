module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)
def NativeFinalValue : Prop := ∀ (R D : Program 2) (G : Program 3)
    (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (g : Nat → List Nat → Nat → Option Nat) (f : Nat → Nat → Nat),
  (∀ seed param, evaluate R (List.Vector.ofFn ![seed,param]) = m seed param) →
  (∀ node param, evaluate D (List.Vector.ofFn ![node,param]) = numbersNumber (d node param)) →
  (∀ node vals param, evaluate G (List.Vector.ofFn ![node,numbersNumber vals,param]) =
    Encodable.encode (g node vals param)) →
  (∀ node param child, child ∈ d node param → m child param < m node param) →
  (∀ node param, g node ((d node param).map (fun child => f child param)) param = some (f node param)) →
  ∀ (seed param : Nat), evaluate (exchange R D G) (List.Vector.ofFn ![seed,param]) = f seed param
/-- Actual program existence from paid original numeric primitives, at ONE
shared R/D/G tuple, with all-vector extension and exact original encoded inputs. -/
def ConcreteSelection : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (R D : Program 2) (G : Program 3),
    (∀ v, evaluate R v = ExchangeNumericSuppliers.rankValue n v) ∧
    (∀ v, evaluate D v = ExchangeNumericSuppliers.depsValue n v) ∧
    (∀ v, evaluate G v = ExchangeNumericSuppliers.layerValue n arity v) ∧
    (∀ v : List.Vector Nat 2, evaluate (exchange R D G) v =
      ExchangeNumericSuppliers.valueAt n arity (v.get 0) (v.get 1)) ∧
    (∀ (window : ExchangeNumericSuppliers.Window n)
      (source target : NumberedAuxiliaryCoding.Code (Fin n)),
      evaluate (exchange R D G) (List.Vector.ofFn ![Encodable.encode (source,target),Encodable.encode window]) =
        (NumberedExchangeCode.codeExchange arity window.1 window.2 source target).toNat)
def InternalFinalGraph : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (R D : Program 2) (G : Program 3)
    (seed param rankValue table out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 R rankValue seed param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) table (suc rankValue) seed param)) →
  (Nonempty (Derivation body Delta (graph2 (exchange R D G) out seed param)) ↔
   Nonempty (Derivation body Delta (graph1 extract out table)))
def InternalSingletonValue : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (R D : Program 2) (G : Program 3)
    (seed param rankValue table pair value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 R rankValue seed param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) table (suc rankValue) seed param)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair z)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair seed value)) →
  Nonempty (Derivation body Delta (graph2 (exchange R D G) value seed param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.Targets
