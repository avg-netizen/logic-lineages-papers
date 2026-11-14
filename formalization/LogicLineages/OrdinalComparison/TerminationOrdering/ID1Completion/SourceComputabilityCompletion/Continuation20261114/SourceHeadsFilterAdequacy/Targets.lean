module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

def InternalFilter : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw out needle symbols types value : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) out raw symbols types)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) ↔
   Nonempty (Derivation body Delta (qualifies raw needle value)))

/-- Actual sourceHeads/member composition, not a new enumeration. Its raw-window
output remains an explicit actual graph premise, not a semantic list assumption. -/
def InternalSourceMember : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw needle symbols types value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow raw symbols types)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)) →
  (Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) needle symbols types)) ↔
   Nonempty (Derivation body Delta (qualifies raw needle value)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.Targets
