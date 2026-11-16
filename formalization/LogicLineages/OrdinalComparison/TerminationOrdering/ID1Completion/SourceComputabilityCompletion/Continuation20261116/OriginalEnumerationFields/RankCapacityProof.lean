module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankCapacityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof InternalTagArithmeticSyntaxProof
open InternalAdditionLawsProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem capacity (index seed param depth frontier node seedRank nodeRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seedRank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hc : Nonempty (Derivation body Delta (graph2 rank nodeRank node param))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded nodeRank index)) := by
  obtain ⟨hcomp⟩ := SubtractionAlignment.Proof.complement body alpha Delta index seedRank depth hb hs
  have hbound := FrontierRank.BoundProof.rankBound depth seed param frontier node seedRank nodeRank hf hm hr hc
  have he : Nonempty (Derivation body Delta (eqn seedRank (add depth index))) :=
    ⟨trans (symm hcomp) (commutativity index depth)⟩
  have ht := PrimaryUncoveredCount.OrderProof.transport (add depth nodeRank) seedRank (add depth nodeRank) (add depth index)
    ⟨refl _⟩ he hbound
  exact FrontierCapacity.Proof.boundedCancel depth nodeRank index ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankCapacityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankCapacityProof
