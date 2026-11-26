module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- ALL raw table codes, literal original finPi instance, including the n=0 table. -/
def NativeTable : Prop := ∀ (n : Nat) (v : List.Vector Nat 1),
  evaluate (tableGuard n) v = (Encodable.decode (α := Fin n → Fin n → Bool) (v.get 0)).isSome.toNat
/-- ALL raw Context codes, original product decoder and default failure. -/
def NativeContext : Prop := ∀ (n : Nat) (v : List.Vector Nat 1),
  evaluate (contextGuard n) v = (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0)).isSome.toNat
/-- Internal actual guard decomposition, not reflection of the native decoder.
The only observation is the actual original pair graph for the Context code. -/
def InternalContext : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw window table : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw window table)) →
  (Nonempty (Derivation body Delta (graph1 (contextGuard n) (numeral 1) raw)) ↔
   Nonempty (Derivation body Delta
    (graph1 (OriginalDecodedWindowValidity.window n) (numeral 1) window ⊓
     graph2 contains (numeral 1) (numeral (tableListCode n)) table)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.Targets
