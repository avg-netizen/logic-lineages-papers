module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalComputabilityDownwardSyntaxProof (domainRename typedRename)
open InternalComputabilityApplicationSyntaxProof (acceptedRename)
open InternalOriginalUniformApplicationTypingApplicationProof (typedGraphRename)
open InternalParameterizedCanonicalResultFoldSyntaxProof (applicationGraphRename)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalSourceApplicationReconstruction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem recoveredRename {alpha beta : Type} (data : Data) (window : Program 1)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex targetFunctionObject vertexObject : OTerm alpha) (j : alpha → beta) :
    (Recovered data window comp context sigma tau
      functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex targetFunctionObject vertexObject).relabel j =
      Recovered data window comp context sigma tau
        (functionObject.relabel j) (argumentObject.relabel j) (outputObject.relabel j)
        (gammaCode.relabel j) (function.relabel j) (argument.relabel j)
        (out.relabel j) (parameter.relabel j) (targetFunction.relabel j) (vertex.relabel j)
        (targetFunctionObject.relabel j) (vertexObject.relabel j) := by
  simp only [Recovered,conjunctionRename,OriginalSourceNeutralApplicationSyntaxProof.recoveredRename,
    typedGraphRename,applicationGraphRename,graph2Rename,typedRename,domainRename,acceptedRename,numeralRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionSyntaxProof
