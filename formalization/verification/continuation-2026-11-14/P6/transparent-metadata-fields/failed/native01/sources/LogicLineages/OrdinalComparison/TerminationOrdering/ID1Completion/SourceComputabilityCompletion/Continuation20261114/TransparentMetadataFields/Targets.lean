module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.Targets
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
def InternalUnary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target ordinary : Bool)
    (node code param raw metadata child : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta (graph2
    (if ordinary then OriginalRawSyntaxTransport.ordinaryConstructor else OriginalRawSyntaxTransport.lambdaConstructor)
    raw metadata child)) →
  FieldsAt body Delta V target node code param (if ordinary then numeral 0 else metadata)
    (if ordinary then metadata else numeral 0) (numeral 0) (numeral 0)
def InternalApplication : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target cons : Bool)
    (node code param raw domain left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    raw domain left right)) →
  FieldsAt body Delta V target node code param domain (numeral 0) (numeral 0) (numeral 0)
def InternalNumbered : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target : Bool)
    (node code param raw rank hd tau base ts extras : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw
    ![rank,hd,tau,base,ts,extras])) →
  FieldsAt body Delta V target node code param tau hd rank ts
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.Targets
