module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def FieldsAt (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha))
    (V : Program 3) (target : Bool) (node code param a h l ts : OTerm alpha) : Prop :=
  Nonempty (Derivation body Delta (graph3 (annotation V target) a node code param)) ∧
  Nonempty (Derivation body Delta (graph3 (head V target) h node code param)) ∧
  Nonempty (Derivation body Delta (graph3 (label V target) l node code param)) ∧
  Nonempty (Derivation body Delta (graph3 (types V target) ts node code param))
def NativeMetadata : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3),
  (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) →
  ∀ (target : Bool) v,
    evaluate (annotation V target) v = TransparentExchangeLayer.fieldValue n arity (if target then 8 else 1) v ∧
    evaluate (head V target) v = TransparentExchangeLayer.fieldValue n arity (if target then 9 else 2) v ∧
    evaluate (label V target) v = TransparentExchangeLayer.fieldValue n arity (if target then 10 else 3) v ∧
    evaluate (types V target) v = TransparentExchangeLayer.fieldValue n arity (if target then 11 else 4) v
/-- Actual conversion graph, never a raw-head/encoded-head equality. -/
def InternalHeadFactor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target : Bool)
    (node code param rawHead encodedHead : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (TransparentMetadataFields.head V target) rawHead node code param)) →
  (Nonempty (Derivation body Delta (graph3 (head V target) encodedHead node code param)) ↔
   Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead encodedHead rawHead)))
/-- Exact numbered metadata with a genuine explicit conversion graph premise. -/
def InternalNumbered : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target : Bool)
    (node code param raw rank rawHead encodedHead tau base ts extras : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw
    ![rank,rawHead,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead encodedHead rawHead)) →
  FieldsAt body Delta V target node code param tau encodedHead rank ts
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.Targets
