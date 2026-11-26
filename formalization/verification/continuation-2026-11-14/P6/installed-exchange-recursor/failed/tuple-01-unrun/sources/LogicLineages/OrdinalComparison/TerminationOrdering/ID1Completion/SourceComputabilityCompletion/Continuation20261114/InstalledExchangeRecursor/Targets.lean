module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion
def SupplierSelection : Prop := ∀ n : Nat, ∃ (V : Program 3) (K : Program 1),
  (∀ v, evaluate V v = validValue n v) ∧ (∀ v, evaluate K v = windowValue n v)
def NativeStructural : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (R D : Program 2) (J V : Program 3) (K : Program 1),
  (∀ v : List.Vector Nat 2, evaluate (ExchangeSelectedRecursor.exchange R D J) v =
    ExchangeNumericSuppliers.valueAt n arity (v.get 0) (v.get 1)) →
  (∀ v, evaluate V v = validValue n v) →
  (∀ v, evaluate K v = windowValue n v) →
  ∀ v, evaluate (structural R D J V K) v = TypedPrimaryEdge.structuralValue n arity v
def InternalFactor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (R D : Program 2) (J V : Program 3) (K : Program 1)
    (source target param node window out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) source target param)) →
  Nonempty (Derivation body Delta (graph3 nodeCode node source target param)) →
  Nonempty (Derivation body Delta (graph1 K window param)) →
  (Nonempty (Derivation body Delta (graph3 (structural R D J V K) out source target param)) ↔
   Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D J) out node window)))
/-- A NEW full tuple installs the explicit original-algorithm structural checker,
while retaining the actual type guard, seeded pool, actual pool length, and all
previous package/representative properties. Original opaque tuples are unchanged. -/
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∃ (Q R D : Program 2) (J V : Program 3) (K : Program 1),
    (∀ v, evaluate Q v = SeededPrimaryPool.candidatesValue n arity v) ∧
    (∀ v, evaluate R v = ExchangeNumericSuppliers.rankValue n v) ∧
    (∀ v, evaluate D v = ExchangeNumericSuppliers.depsValue n v) ∧
    (∀ v, evaluate J v = ExchangeNumericSuppliers.layerValue n arity v) ∧
    (∀ v, evaluate V v = validValue n v) ∧
    (∀ v, evaluate K v = windowValue n v) ∧
    let B := structural R D J V K
    (∀ v, evaluate B v = TypedPrimaryEdge.structuralValue n arity v) ∧
    let T := OriginalTypedDecoder.target H G
    let P := SeededPrimaryPool.pool T Q
    let E := TypedPrimaryEdge.edge B
    let L := SeededPrimaryPool.primary T Q E
    let q := Membership.inputs p H G L (TransparentCandidate.candidate T)
    TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P E ∧
    Membership.ListCalibrated n arity L ∧
    (∀ v : List.Vector Nat 2, evaluate q.base.oldRepresentative v = evaluate p.base.oldRepresentative v) ∧
    GlobalSourcePackage.InputsCalibrated n arity q ∧
    OriginalRankGuardedRepresentative.Properties n arity q H G W
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Targets
