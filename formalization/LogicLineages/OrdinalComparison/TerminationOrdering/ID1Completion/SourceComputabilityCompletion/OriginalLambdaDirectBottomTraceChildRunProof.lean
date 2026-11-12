module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace

theorem actualChildRun : OriginalLambdaDirectBottomTraceChildRunTargets.ActualChildRun := by
 intro source leaf body alpha Delta s t cert parameter code tail childS childT childCert childParam next out hp ht hc hl hr hf
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,childParam]
 have hleft := OriginalHereditaryLambdaChildRunProof.strippedPath xs childCert code tail hp ht hc
 have hpath := unaryValue InternalUnpair.left (.projection 2) tail childCert ys hleft (projectionValue 2 ys)
 have hrun := binaryValue (InternalRawListRepeat.repeatProgram (transition source leaf))
  OriginalHereditaryLambda.path OriginalHereditaryLambda.live out tail next ys hr hpath hl
 have hrecognized := unaryValue (finish source leaf) (run source leaf) (suc z) out ys hf hrun
 exact InternalApplicationStepPeelSupportProof.andIntro hleft hrecognized
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
