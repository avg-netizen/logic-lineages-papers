module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.BoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.CapacityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (suc sucRelabel eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalGraphCompositionFunctionalityProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem capacityAt (n : Nat) (index seed param depth frontier node seedRank nodeRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seedRank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R nodeRank node param))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded nodeRank index)) := by
  obtain ⟨he⟩ := SubtractionAlignment.Proof.complement body alpha Delta index seedRank depth hb hs
  have hbound := OriginalEnumerationCacheCoherence.FrontierRank.BoundProof.rankBound n body alpha Delta depth seed param frontier node seedRank nodeRank hr hf hm hc
  have ht := PrimaryUncoveredCount.OrderProof.transport (OrdinaryArithmetic.addTerm depth nodeRank) seedRank
    (OrdinaryArithmetic.addTerm depth nodeRank) (OrdinaryArithmetic.addTerm depth index)
    ⟨InternalTagArithmeticSupportProof.refl _⟩
    ⟨InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.symm he) (InternalAdditionCancellationProof.commutativity index depth)⟩ hbound
  exact FrontierCapacity.Proof.boundedCancel depth nodeRank index ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.CapacityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.CapacityProof
