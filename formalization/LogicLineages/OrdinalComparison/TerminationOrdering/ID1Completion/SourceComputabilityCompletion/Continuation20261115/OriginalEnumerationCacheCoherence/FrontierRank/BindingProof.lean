module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.BindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Continuation20261114
open InductionDefinitions InductionSyntaxProof
open InternalClosedProgramsBindingProof
theorem rowApply (n : Nat) (depth seed param frontier child seedRank childRank : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtCount n depth)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R childRank child param))) :
    Nonempty (Derivation body Delta (result depth seedRank childRank)) := by
  obtain ⟨h⟩ := elimination body alpha 6 Delta (matrix n depth)
    (fun i => emb (![seed,param,frontier,child,seedRank,childRank] i)) h
  rw [matrixWitness] at h
  obtain ⟨hs⟩ := andIntro (andIntro hr hf) (andIntro hm hc)
  exact ⟨Derivation.implicationElimination h hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.BindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.BindingProof
