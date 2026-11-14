module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeResults : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3),
  (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) →
  ∀ (target : Bool) v,
    evaluate (result V target) v =
      TransparentExchangeLayer.fieldValue n arity (if target then 18 else 17) v
/-- Actual ordinary constructor and head-pair evidence remove field-output premises.
The concrete branch builds the original result type; it is not semantic reflection. -/
def InternalOrdinary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target : Bool) (tag : Fin 6)
    (node code param raw rawHead payload base out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw rawHead base)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawHead (numeral tag.val) payload)) →
  (Nonempty (Derivation body Delta (graph3 (result V target) out node code param)) ↔
   Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.branchResult tag.val) out payload)))
def InternalNumbered : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target : Bool) (tag : Fin 6)
    (node code param raw rank rawHead payload tau base ts extras out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw
    ![rank,rawHead,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawHead (numeral tag.val) payload)) →
  (Nonempty (Derivation body Delta (graph3 (result V target) out node code param)) ↔
   Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.branchResult tag.val) out payload)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.Targets
