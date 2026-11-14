module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def NativeOriginal : Prop := ∀ (n : Nat) (base target : NumberedAuxiliaryCoding.Code (Fin n)),
  evaluate check (List.Vector.ofFn ![NumberedLeastCodeRepresentative.codeNumber base,NumberedLeastCodeRepresentative.codeNumber target]) =
    (NumberedExchangeCode.argumentPermutation base target).toNat

/-- Rejection comes from the literal Option gates, not validity reflection. -/
def InternalNone : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (base target : OTerm alpha),
  (Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (numeral 0) base (numeral 0))) →
   Nonempty (Derivation body Delta (graph2 check (numeral 0) base target))) ∧
  (∀ sourceList : OTerm alpha,
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc sourceList) base (numeral 0))) →
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (numeral 0) target (numeral 0))) →
    Nonempty (Derivation body Delta (graph2 check (numeral 0) base target)))

def InternalSome : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (base target sourceList targetList out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc sourceList) base (numeral 0))) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc targetList) target (numeral 0))) →
  (Nonempty (Derivation body Delta (graph2 check out base target)) ↔
   Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation out sourceList targetList)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Targets
