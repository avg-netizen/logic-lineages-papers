module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniformStepQuotientProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open ClaudeSupervisedCompletion OriginalNeutralQuotient
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem windowRename {alpha beta : Type} (window : Program 1)
    (input parameter : OTerm alpha) (j : alpha → beta) :
    (OriginalFunctionNeutrality.windowGraph window input parameter).relabel j =
      OriginalFunctionNeutrality.windowGraph window (input.relabel j) (parameter.relabel j) := by
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem stepRename {alpha beta : Type} (data : Data) (oldStep : Program 4)
    (source target certificate parameter : OTerm alpha) (j : alpha → beta) :
    (stepAccepted data oldStep source target certificate parameter).relabel j =
      stepAccepted data oldStep (source.relabel j) (target.relabel j)
        (certificate.relabel j) (parameter.relabel j) := by
  simp only [stepAccepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem peeledRename {alpha beta : Type} (endpoint : Program 6) (oldStep : Program 4)
    (d e arrow f g a k child state S T K parameter : OTerm alpha) (j : alpha → beta) :
    (InverseGuardTargets.Peeled endpoint oldStep d e arrow f g a k child
      InternalOriginalStepGuard.one state S T K parameter).relabel j =
      InverseGuardTargets.Peeled endpoint oldStep
        (d.relabel j) (e.relabel j) (arrow.relabel j) (f.relabel j) (g.relabel j)
        (a.relabel j) (k.relabel j) (child.relabel j) InternalOriginalStepGuard.one
        (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j) := by
  simp only [InverseGuardTargets.Peeled,InverseGuardTargets.Recovered,
    conjunctionRename,graph2Rename,graph3Rename,liftedCheckerPremisesRename,
    transitionGraphRename,checkerGraphRename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem recoveredRename {alpha beta : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter S T K state d e arrow f g a k child F G A : OTerm alpha)
    (j : alpha → beta) :
    (Recovered data oldStep x y certificate parameter S T K state d e arrow f g a k child F G A).relabel j =
      Recovered data oldStep (x.relabel j) (y.relabel j) (certificate.relabel j)
        (parameter.relabel j) (S.relabel j) (T.relabel j) (K.relabel j) (state.relabel j)
        (d.relabel j) (e.relabel j) (arrow.relabel j) (f.relabel j) (g.relabel j)
        (a.relabel j) (k.relabel j) (child.relabel j) (F.relabel j) (G.relabel j) (A.relabel j) := by
  simp only [Recovered,conjunctionRename,selectorsRename,requirementsRename,graph3Rename,
    peeledRename,OriginalUniformStepQuotientProof.recoveredRename,foldGraphRename,graph4Rename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientSyntaxProof
