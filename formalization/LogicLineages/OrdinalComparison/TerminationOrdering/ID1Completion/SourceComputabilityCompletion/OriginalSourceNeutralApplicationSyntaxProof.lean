module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalComputabilityDownwardSyntaxProof (domainRename)
open InternalComputabilityApplicationSyntaxProof (acceptedRename)
open InternalOriginalUniformApplicationTypingApplicationProof (applicationPremisesRename)
open InternalParameterizedCanonicalResultFoldSyntaxProof (applicationGraphRename)
open OriginalNeutralApplicationSyntaxProof (inputPremisesRename)
open GuardedSourceSyntaxProof (numeralRename)
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open OriginalSourceNeutralApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem negationRename {alpha beta : Type} (phi : Formula alpha) (j : alpha → beta) :
    phi.not.relabel j = (phi.relabel j).not := rfl

theorem equivalenceRename {alpha beta : Type} (phi chi : Formula alpha) (j : alpha → beta) :
    (phi.iff chi).relabel j = (phi.relabel j).iff (chi.relabel j) := rfl

theorem nonLambdaObjectRename {alpha beta : Type} (object : OTerm alpha) (j : alpha → beta) :
    (nonLambdaObject object).relabel j = nonLambdaObject (object.relabel j) := by
  simp only [nonLambdaObject,negationRename,graph1Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem recoveredRename {alpha beta : Type} (data : Data) (window : Program 1)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter : OTerm alpha)
    (j : alpha → beta) :
    (Recovered data window comp context sigma tau
      functionObject argumentObject outputObject gammaCode function argument out parameter).relabel j =
      Recovered data window comp context sigma tau
        (functionObject.relabel j) (argumentObject.relabel j) (outputObject.relabel j)
        (gammaCode.relabel j) (function.relabel j) (argument.relabel j)
        (out.relabel j) (parameter.relabel j) := by
  simp only [Recovered,conjunctionRename,domainRename,acceptedRename,graph2Rename,
    applicationPremisesRename,inputPremisesRename,applicationGraphRename,numeralRename,
    equivalenceRename,nonLambdaObjectRename,OriginalNonLambdaApplication.nonLambda,
    OriginalConstructorShape.tagGraph,negationRename,graph1Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
