module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BindingProof
open Continuation20261114
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

open InductionDefinitions InductionSyntaxProof
open InternalClosedProgramsBindingProof
theorem rowApply (depth seed param frontier child seedRank childRank : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtCount depth)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param))) :
    Nonempty (Derivation body Delta (result depth seedRank childRank)) := by
  obtain ⟨h⟩ := elimination body alpha 6 Delta (matrix depth)
    (fun i => emb (![seed,param,frontier,child,seedRank,childRank] i)) h
  rw [matrixWitness] at h
  obtain ⟨hp⟩ := andIntro (andIntro (andIntro hf hm) hs) hc
  exact ⟨Derivation.implicationElimination h hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BindingProof
