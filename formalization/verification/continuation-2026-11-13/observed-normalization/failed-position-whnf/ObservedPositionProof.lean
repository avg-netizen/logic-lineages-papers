module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedClassCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationPointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedPositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open UniformCertificateCompletion ObservedClassDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem position (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) (out input typ parameter cutoff : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter)))
    (hr : Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (OriginalClassContextAllPositionObserver.positionTest
        (OriginalStructuralClassKeyDefinitions.key p H G W)) (suc z) cutoff input out parameter)) := by
  let K := OriginalStructuralClassKeyDefinitions.key p H G W
  apply programCases (OriginalClassContextAllPositionObserver.positionObservation K)
    (Fin.cons cutoff (Fin.cons input (Fin.cons parameter Fin.elim0))) _
  intro beta j Theta value hj hv
  simp only [graph4Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hv
  have hargs : Nonempty (Derivation body Theta
      (premises p H G W P (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j))) := by
    simpa only [premises, conjunctionRename, OriginalFunctionNeutrality.windowGraph,
      OriginalVariableRepresentative.windowGraph, graph2Rename,
      InternalOriginalStepGuard.one, sucRelabel, zRelabel, sourcePremisesRename, foldGraphRename]
      using renameInto ha j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [OriginalIndexedObserverRangeSyntaxProof.rangeRename] at hr'
  obtain ⟨law⟩ := OriginalAllPositionStructuralTraversalProof.actualFinal
    p H G W P body beta Theta (out.relabel j) (input.relabel j) (typ.relabel j)
      (parameter.relabel j) value (cutoff.relabel j)
  obtain ⟨args⟩ := andIntro hargs hr'
  obtain ⟨hv⟩ := hv
  have ho := Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law args)) hv
  exact OriginalAllPositionRelationPointProof.atCommon K (cutoff.relabel j)
    (input.relabel j) (out.relabel j) (parameter.relabel j) value ⟨hv⟩ ⟨ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedPositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedPositionProof
