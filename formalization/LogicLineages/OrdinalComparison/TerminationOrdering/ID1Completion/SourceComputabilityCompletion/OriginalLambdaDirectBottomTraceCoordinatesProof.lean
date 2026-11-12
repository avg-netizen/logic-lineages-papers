module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceCoordinatesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalLambdaGuardLeafInternalChildProof (fourTuple)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualChildCoordinates : OriginalLambdaDirectBottomTraceCoordinatesTargets.ActualChildCoordinates := by
 intro source leaf body alpha Delta s t cert parameter next psi hh hc k
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hguard := andLeft (conjunctionRecover (OriginalTransparentLambdaStep.hopGuard source) leaf xs hh)
 have hlambda := andRight (conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) _ xs hguard)
 have hmatch := andRight (conjunctionRecover OriginalLambdaGuardLeaf.sourceLambda _ xs hlambda)
 have hpath := andRight (conjunctionRecover OriginalLambdaGuardLeaf.matchingTarget OriginalHereditaryLambda.lamPath xs hmatch)
 apply programCompositionCases OriginalHereditaryLambda.live
  ![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
    OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] next xs psi hc
 intro beta rho ys Theta hrho ht hg
 have hp := renameInto hpath rho Theta hrho
 simp only [programRename,sucRelabel,zRelabel] at hp ht
 have hprefix := OriginalHereditaryLambdaPrefixProof.recoverPrefix (fun i => (xs i).relabel rho) (ys 2) hp (hg 2)
 have hxs : (fun i => (xs i).relabel rho) =
    ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun u => Fin.elim0 u)))) i
 rw [hxs] at hg
 have hstrip := unaryRecover OriginalLambdaGuardLeaf.stripCertificate (.projection 2)
  (ys 2) (cert.relabel rho) ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho]
  (hg 2) (projectionValue (2 : Fin 4) (![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho] : Fin 4 → OTerm beta))
 rw [← fourTuple ys] at ht
 exact k beta rho Theta (ys 0) (ys 1) (ys 2) (ys 3) hrho (hg 0) (hg 1) (hg 2) (hg 3) hprefix hstrip ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceCoordinatesProof
