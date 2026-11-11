module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open OriginalSourceNeutralApplicationPath
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem pathInputsRename {alpha beta : Type} (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty)
    (F A X Y witness gammaCode function argument x y parameter : OTerm alpha) (j : alpha → beta) :
    (PathInputs data window oldStep src comp context sigma tau
      F A X Y witness gammaCode function argument x y parameter).relabel j =
      PathInputs data window oldStep src comp context sigma tau
        (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j) (witness.relabel j)
        (gammaCode.relabel j) (function.relabel j) (argument.relabel j)
        (x.relabel j) (y.relabel j) (parameter.relabel j) := by
  simp only [PathInputs,conjunctionRename,OriginalSourceNeutralApplicationSyntaxProof.recoveredRename,
    OriginalSourceNeutralApplicationSyntaxProof.nonLambdaObjectRename,
    OriginalNonLambdaApplicationSyntaxProof.nonLambdaRename,
    InternalComputabilityDownwardSyntaxProof.certificateRename,graph2Rename,
    InternalParameterizedPathCheckerSyntaxProof.positiveRename]

theorem recoveredPrefixRename {alpha beta : Type} (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty)
    (F A X Y witness gammaCode function argument x y parameter raw tail vertex certificate : OTerm alpha)
    (j : alpha → beta) :
    (RecoveredPrefix data window oldStep src comp context sigma tau
      F A X Y witness gammaCode function argument x y parameter raw tail vertex certificate).relabel j =
      RecoveredPrefix data window oldStep src comp context sigma tau
        (F.relabel j) (A.relabel j) (X.relabel j) (Y.relabel j) (witness.relabel j)
        (gammaCode.relabel j) (function.relabel j) (argument.relabel j)
        (x.relabel j) (y.relabel j) (parameter.relabel j) (raw.relabel j)
        (tail.relabel j) (vertex.relabel j) (certificate.relabel j) := by
  simp only [RecoveredPrefix,conjunctionRename,pathInputsRename,
    OriginalNonLambdaApplicationPathSyntaxProof.firstStepRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathSyntaxProof
