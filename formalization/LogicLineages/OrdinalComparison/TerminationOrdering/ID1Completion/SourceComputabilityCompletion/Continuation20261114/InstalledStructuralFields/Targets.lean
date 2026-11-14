module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion
def LambdaAt (U : Fin 19 → Program 3) (V : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node code param source target sigma tau q r h0 t0 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  (Nonempty (Derivation body Delta (graph3 (StructuralExchangeFields.layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta (eqn sigma tau ⊓ eqn h0 (numeral 1))))
def InternalLambda : Prop := ∀ (U : Fin 19 → Program 3) (V : Program 3), LambdaAt U V
def ApplicationAt (U : Fin 19 → Program 3) (V : Program 3) : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (cons : Bool)
    (node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    source sigma q a)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    target tau r b)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  (Nonempty (Derivation body Delta (graph3 (StructuralExchangeFields.layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta (eqn sigma tau ⊓
     ((eqn a b ⊓ eqn h0 (numeral 1)) ⊔ (eqn q r ⊓ eqn h3 (numeral 1))))))
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
    let J := StructuralExchangeFields.layer U V
    (∀ v, evaluate J v = ExchangeNumericSuppliers.layerValue n arity v) ∧
    LambdaAt U V ∧
    ApplicationAt U V ∧
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.Targets
