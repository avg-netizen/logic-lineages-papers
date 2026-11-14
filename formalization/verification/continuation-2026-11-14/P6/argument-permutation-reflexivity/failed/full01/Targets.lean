module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)

/-- Actual arbitrary raw candidate list, not a semantic list or count oracle. -/
def InternalAllCounts : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (candidates list : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) candidates list list))

def InternalPermutation : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (list : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) list list))

/-- Original optional extraction must actually be defined. This hypothesis is
not replaced by a native decoding fact or by assumed typed correctness. -/
def InternalOriginal : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (base list : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0))) →
  Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base base))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.Targets
