module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SimpleProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalHeadWindow
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open SupportProof
theorem simple : Targets.InternalSimple := by
  intro n arity body alpha Delta tag raw payload result symbols types hp hr
  let t : Fin 6 := ⟨tag.val, by omega⟩
  have hd := OriginalHeadWindow.InternalProof.internalBranch n arity body alpha Delta t raw payload symbols types (numeral 1) hp
  have h4 : tag.val ≠ 4 := by omega
  have h5 : tag.val ≠ 5 := by omega
  have he : branchWindow n arity tag.val = typeMember
      (.composition (OriginalHeadResult.branchResult tag.val) (fun _ : Fin 1 => .projection 0)) := by
    simp only [branchWindow,if_neg h4,if_neg h5]
  change Nonempty (Derivation body Delta (graph3 (window n arity) (numeral 1) raw symbols types)) ↔
    Nonempty (Derivation body Delta (graph3 (branchWindow n arity tag.val) (numeral 1) payload symbols types)) at hd
  rw [he] at hd
  exact hd.trans (typeFactor _ payload symbols types result (resultValue tag.val payload symbols types result hr))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SimpleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SimpleProof
