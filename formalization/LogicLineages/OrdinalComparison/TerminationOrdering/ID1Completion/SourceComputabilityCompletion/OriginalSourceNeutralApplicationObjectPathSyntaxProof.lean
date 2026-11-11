module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof (equalEqn)
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalOriginalUniformApplicationTypingApplicationProof (typedGraphRename)
open InternalParameterizedCanonicalResultFoldSyntaxProof (applicationGraphRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The added Object reconstruction continuation retains every field of
the accepted aligned raw record under the same composed renaming. -/
theorem alignedRecoveredRename {alpha beta : Type} (data : Data) (oldStep : Program 4)
    (arrow d e function argument x y certificate parameter
      S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut : OTerm alpha) (j : alpha → beta) :
    (OriginalNeutralApplicationEdge.Recovered data oldStep
      arrow d e function argument x y certificate parameter
      S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut).relabel j =
      OriginalNeutralApplicationEdge.Recovered data oldStep
        (arrow.relabel j) (d.relabel j) (e.relabel j) (function.relabel j) (argument.relabel j)
        (x.relabel j) (y.relabel j) (certificate.relabel j) (parameter.relabel j)
        (S.relabel j) (T.relabel j) (K.relabel j) (state.relabel j)
        (rawD.relabel j) (rawE.relabel j) (rawArrow.relabel j)
        (rawFunction.relabel j) (rawTarget.relabel j) (rawArgument.relabel j)
        (rawStep.relabel j) (child.relabel j) (functionOut.relabel j)
        (targetFunctionOut.relabel j) (canonicalArgument.relabel j) (argumentOut.relabel j) := by
  simp only [OriginalNeutralApplicationEdge.Recovered,conjunctionRename,
    OriginalNeutralQuotientSyntaxProof.recoveredRename,OriginalNeutralApplicationSyntaxProof.recoveredRename,
    equalEqn,eqnRelabel,UniformCertificateCompletion.SupportProof.edgeRename,
    typedGraphRename,applicationGraphRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathSyntaxProof
