module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion
/-- Includes original fields, headMove, and head-result codes, not a selected
complete exchange function. All malformed/default branches are retained. -/
def PrimitiveFields : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (TransparentExchangeLayer.validValue n) ∧
  ∀ i : Fin 19, Primrec (TransparentExchangeLayer.fieldValue n arity i)
def SupplierSelection : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (U : Fin 19 → Program 3) (V : Program 3),
    (∀ i v, evaluate (U i) v = TransparentExchangeLayer.fieldValue n arity i v) ∧
    (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) ∧
    (∀ v, evaluate (TransparentExchangeLayer.optional U V) v = ExchangeNumericSuppliers.layerValue n arity v)
/-- Same selected U/V, with actual runtime field/guard/cons graph premises.
This does not assert internal semantic correctness for those field suppliers. -/
def LambdaAt (U : Fin 19 → Program 3) (V : Program 3) : Prop :=
  ∀ (bodyFormula : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node code param head tail : OTerm alpha) (xs : Fin 19 → OTerm alpha),
  Nonempty (Derivation bodyFormula Delta (graph3 V (numeral 1) node code param)) →
  (∀ i, Nonempty (Derivation bodyFormula Delta
    (graph3 (TransparentExchangeLayer.fields U i) (xs i) node code param))) →
  Nonempty (Derivation bodyFormula Delta (eqn (xs 0) (numeral 1))) →
  Nonempty (Derivation bodyFormula Delta (eqn (xs 7) (numeral 1))) →
  Nonempty (Derivation bodyFormula Delta (graph2 InternalListCodec.consCode code head tail)) →
  (Nonempty (Derivation bodyFormula Delta
    (graph3 (TransparentExchangeLayer.optional U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation bodyFormula Delta (eqn (xs 1) (xs 8) ⊓ eqn head (numeral 1))))
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∃ (Q R D : Program 2) (U : Fin 19 → Program 3) (V C : Program 3) (K : Program 1),
    (∀ v, evaluate Q v = SeededPrimaryPool.candidatesValue n arity v) ∧
    (∀ v, evaluate R v = ExchangeNumericSuppliers.rankValue n v) ∧
    (∀ v, evaluate D v = ExchangeNumericSuppliers.depsValue n v) ∧
    (∀ i v, evaluate (U i) v = TransparentExchangeLayer.fieldValue n arity i v) ∧
    (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) ∧
    (∀ v, evaluate C v = InstalledExchangeRecursor.validValue n v) ∧
    (∀ v, evaluate K v = InstalledExchangeRecursor.windowValue n v) ∧
    let J := TransparentExchangeLayer.optional U V
    (∀ v, evaluate J v = ExchangeNumericSuppliers.layerValue n arity v) ∧
    LambdaAt U V ∧
    let B := InstalledExchangeRecursor.structural R D J C K
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.Targets
