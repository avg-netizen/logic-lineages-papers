module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankCapacityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.RankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rankDecrease (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (key param deps child parentRank childRank : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank parentRank key param)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank)) :=
  RankDescentProof.descent key param deps child parentRank childRank hp hd hm hc

theorem capacityAt (index seed param depth frontier node seedRank nodeRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank seedRank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seedRank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank nodeRank node param))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded nodeRank index)) :=
  RankCapacityProof.capacity index seed param depth frontier node seedRank nodeRank hr hb hs hf hm hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.RankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.RankProof
