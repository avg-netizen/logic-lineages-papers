module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def NativeField : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3),
  (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) →
  ∀ v, evaluate (move n arity V) v = TransparentExchangeLayer.fieldValue n arity 16 v

def NativeFields : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (U : Fin 19 → Program 3) (V : Program 3),
  (∀ i v, evaluate (U i) v = TransparentExchangeLayer.fieldValue n arity i v) →
  (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) →
  (∀ i v, evaluate (fields n arity U V i) v = TransparentExchangeLayer.fieldValue n arity i v) ∧
  (∀ v, evaluate (layer n arity U V) v = ExchangeNumericSuppliers.layerValue n arity v)

def InternalOrdinary : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3)
    (node code param source target f base g dest symbolsCode typesCode out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbolsCode typesCode)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)) →
  (Nonempty (Derivation body Delta (graph3 (move n arity V) out node code param)) ↔
   Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) out
     ![f,base,g,dest,symbolsCode,typesCode])))

def InternalNumbered : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3)
    (node code param source target k f tau base ts extras l g rho dest us other symbolsCode typesCode out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbolsCode typesCode)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,rho,dest,us,other])) →
  (Nonempty (Derivation body Delta (graph3 (move n arity V) out node code param)) ↔
   Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) out
     ![f,base,g,dest,symbolsCode,typesCode])))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.Targets
