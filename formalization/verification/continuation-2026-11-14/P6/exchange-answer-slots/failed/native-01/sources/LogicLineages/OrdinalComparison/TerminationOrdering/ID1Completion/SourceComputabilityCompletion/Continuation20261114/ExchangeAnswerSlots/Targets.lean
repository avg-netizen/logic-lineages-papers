module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original getD default false, exact-one conversion, every numeric list code.
The consuming positions are 0 and 3, but calibration is uniform in the slot. -/
def NativeSlots : Prop := ∀ (k : Nat) (v : List.Vector Nat 3),
  evaluate (answer k) v =
    ((((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []).map
      (fun value => value == 1)).getD k false).toNat
def InternalLeft : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (node code param head tail : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
  (Nonempty (Derivation body Delta (graph3 (answer 0) (numeral 1) node code param)) ↔
   Nonempty (Derivation body Delta (eqn head (numeral 1))))
/-- Actual right recursive answer is position THREE, not the neighboring cross
entry. Four explicit original cons graphs witness the exact dependency order. -/
def InternalRight : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (node code param h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  (Nonempty (Derivation body Delta (graph3 (answer 3) (numeral 1) node code param)) ↔
   Nonempty (Derivation body Delta (eqn h3 (numeral 1))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.Targets
