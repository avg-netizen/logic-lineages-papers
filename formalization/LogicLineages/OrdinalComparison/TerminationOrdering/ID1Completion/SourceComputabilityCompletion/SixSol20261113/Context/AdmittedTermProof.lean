module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTagBridgesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLeavesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalListCodecSupportProof (consGraphRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ChildContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem actual : AdmittedTermContentTargets.ActualTermReturn := by
  intro Q H M W body alpha Delta input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned hi hparameter ha harity he hscan hm hf hs hret
  apply OriginalTypedDecoderTransportTagSupportProof.rawTagCases raw _
  · intro beta j Theta i payload hj htag hpair
    rw [graph2Rename]
    have hi' := renameInto hi j Theta hj
    have hparameter' := renameInto hparameter j Theta hj
    have ha' := renameInto ha j Theta hj
    have harity' := renameInto harity j Theta hj
    have he' := renameInto he j Theta hj
    have hscan' := renameInto hscan j Theta hj
    have hm' := renameInto hm j Theta hj
    have hf' := renameInto hf j Theta hj
    have hs' := renameInto hs j Theta hj
    have hret' := renameInto hret j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret'
    revert htag hpair
    refine Fin.cases ?_ ?_ i
    · intro htag hpair
      exact AdmittedLeavesProof.variableCase Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) payload hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hpair
    · intro i
      refine Fin.cases ?_ ?_ i
      · intro htag hpair
        exact AdmittedTagBridgesProof.lambdaCase Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' htag
      · intro i
        refine Fin.cases ?_ ?_ i
        · intro htag hpair
          exact AdmittedTagBridgesProof.applicationCase Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' htag
        · intro i
          refine Fin.cases ?_ ?_ i
          · intro htag hpair
            exact AdmittedLeavesProof.bottomCase Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) payload hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hpair
          · intro i
            refine Fin.cases ?_ ?_ i
            · intro htag hpair
              exact AdmittedTagBridgesProof.ordinaryCase Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' htag
            · intro i
              refine Fin.cases ?_ ?_ i
              · intro htag hpair
                exact AdmittedTagBridgesProof.numberedCase Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' htag
              · intro i
                refine Fin.cases ?_ ?_ i
                · intro htag hpair
                  exact OriginalUniverseDecoderTransportRejectedProof.termSix H M W (raw.relabel j) payload (typ.relabel j) (gamma.relabel j) (c.relabel j) _ hpair ha'
                · intro i
                  refine Fin.cases ?_ ?_ i
                  · intro htag hpair
                    exact OriginalUniverseDecoderTransportRejectedProof.termSeven H M W (raw.relabel j) payload (typ.relabel j) (gamma.relabel j) (c.relabel j) _ hpair ha'
                  · intro i
                    exact Fin.elim0 i
  · intro beta j Theta tag payload hj hpair hunknown
    rw [graph2Rename]
    have ha' := renameInto ha j Theta hj
    rw [termAcceptedRename] at ha'
    exact OriginalUniverseDecoderTransportRejectedProof.unknown H M W false (raw.relabel j) tag payload (typ.relabel j) (gamma.relabel j) (c.relabel j) _ hpair hunknown ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermProof.actual
