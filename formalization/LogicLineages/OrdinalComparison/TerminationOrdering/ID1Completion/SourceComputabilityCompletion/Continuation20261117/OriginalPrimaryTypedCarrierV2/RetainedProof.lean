module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.TargetFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.PoolProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.RetainedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atContext (H G : Program 1) (seed param candidate context : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed param)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left context param)))
    (hr : Nonempty (Derivation body Delta (OriginalCandidates.Targets.retained H seed param candidate))) :
    Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) candidate param)) := by
  apply OriginalCandidates.RetainedBindingProof.cases H seed param candidate _ hr
  intro beta j Theta gamma value hj hg hv hn
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have ht' := renameInto ht j Theta hj
  have hc' := renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hc'
  have hG := TargetFieldsProof.seedGuard H G (seed.relabel j) (param.relabel j) (context.relabel j) ht' hc'
  have hgamma := unaryRecover InternalUnpair.right (.projection 1) gamma (param.relabel j)
    ![seed.relabel j,param.relabel j] hg (projectionValue 1 ![seed.relabel j,param.relabel j])
  exact TargetFieldsProof.rebuild H G (candidate.relabel j) (param.relabel j) gamma (context.relabel j)
    hgamma hc' hG (BooleanProof.packedNonzero H (candidate.relabel j) gamma value hv hn)

theorem accepted (H G : Program 1) (seed param candidate : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed param)))
    (hr : Nonempty (Derivation body Delta (OriginalCandidates.Targets.retained H seed param candidate))) :
    Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) candidate param)) := by
  apply InternalAcceptanceSupportProof.programCases InternalUnpair.left ![param] _
  intro beta j Theta context hj hc
  have hx : (fun i => (![param] i).relabel j) = ![param.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hc
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have ht' := renameInto ht j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht'
  rw [OriginalCandidates.RetainedSyntaxProof.retainedRename] at hr'
  exact atContext H G (seed.relabel j) (param.relabel j) (candidate.relabel j) context ht' hc hr'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.RetainedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.RetainedProof
