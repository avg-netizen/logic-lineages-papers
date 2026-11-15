module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
/-- One-sided preservation of every ACTUAL first-match Option lookup on a key
occurring in the literal key-list. Quantifies zero as well as successor outputs. -/
def agreementMatrix {alpha : Type} (keys left right : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (graph2 contains (numeral 1) (keys.relabel Sum.inl) (.var (.inr 0))).imp
    ((graph2 ExchangeMapGraph.lookup (.var (.inr 1)) (left.relabel Sum.inl) (.var (.inr 0))).imp
      (graph2 ExchangeMapGraph.lookup (.var (.inr 1)) (right.relabel Sum.inl) (.var (.inr 0))))
def lookupAgreement {alpha : Type} (keys left right : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (agreementMatrix keys left right)
/-- Extensionality of the original omission-preserving mapGraph, including
all raw list codes, duplicate keys and Some0. This is a compositional lemma,
not an assumption or proof of agreement for independently rooted caches. -/
def InternalTransport : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (keys left right out : OTerm alpha),
  Nonempty (Derivation body Delta (lookupAgreement keys left right)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph out keys left)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph out keys right))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Targets
