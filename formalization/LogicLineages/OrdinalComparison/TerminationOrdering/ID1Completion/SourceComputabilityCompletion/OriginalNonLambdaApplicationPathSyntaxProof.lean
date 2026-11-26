module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion OriginalNonLambdaApplicationPath
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem firstStepRename {alpha beta : Type} (data : Data) (oldStep : Program 4)
    (x y pathCode parameter raw tail vertex certificate : OTerm alpha) (j : alpha → beta) :
    (FirstStep data oldStep x y pathCode parameter raw tail vertex certificate).relabel j =
      FirstStep data oldStep (x.relabel j) (y.relabel j) (pathCode.relabel j)
        (parameter.relabel j) (raw.relabel j) (tail.relabel j)
        (vertex.relabel j) (certificate.relabel j) := by
  simp only [FirstStep,conjunctionRename,graph2Rename,
    UniformCertificateCompletion.SupportProof.edgeRename,
    InternalParameterizedPathCheckerSyntaxProof.pathRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathSyntaxProof
