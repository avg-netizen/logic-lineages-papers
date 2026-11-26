module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
def InternalBasic : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (which : Fin 2) (symbols types out head : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing head (numeral (basicTag which)) (numeral 0))) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out head))

def InternalUnary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (which : Fin 2) (symbols types out head tau : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing head (numeral (unaryTag which)) tau)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) types tau)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out head))

def InternalApplication : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (symbols types out head payload sigma tau : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload sigma tau)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing head (numeral 4) payload)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) types sigma)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) types tau)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out head))

def InternalRanked : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (symbols types out head symbol : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing head (numeral 5) symbol)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) symbols symbol)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out head))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.Targets
