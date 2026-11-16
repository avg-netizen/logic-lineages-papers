module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.RankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rankValue (raw param : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank raw raw param)) :=
  projectionValue 0 ![raw,param]

theorem rankEqual (raw param value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank value raw param))) :
    Nonempty (Derivation body Delta (eqn value raw)) :=
  valueUnique OriginalEnumerationDepth.rank value raw ![raw,param] h (rankValue raw param)

theorem rankDecrease (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw param deps child parentRank childRank : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank parentRank raw param)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank)) :=
  InternalOriginalPairingOrderArithmeticProof.strictTransport childRank parentRank child raw
    (rankEqual child param childRank hc) (rankEqual raw param parentRank hp)
    (ArgumentEntriesDependencyDescent.Proof.dependencyDescent body alpha Delta raw param deps child hd hm)

theorem capacityAt (index seed param depth frontier node seedRank nodeRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank seedRank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seedRank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationDepth.dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank nodeRank node param))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded nodeRank index)) := by
  have he := rankEqual seed param seedRank hr
  have hb' := PrimaryUncoveredCount.OrderProof.transport index seedRank index seed ⟨refl index⟩ he hb
  have hs' := InternalEqualityTestSubtractionSupportProof.subTransport depth index seedRank index seed
    ⟨refl index⟩ he hs
  have hcap := FrontierCapacity.Proof.capacity body alpha Delta index seed param depth frontier node hb' hs' hf hm
  obtain ⟨hc⟩ := rankEqual node param nodeRank hc
  exact PrimaryUncoveredCount.OrderProof.transport node index nodeRank index ⟨symm hc⟩ ⟨refl index⟩ hcap
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.RankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.RankProof
