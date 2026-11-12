module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem runProjection : OriginalHereditaryEvaluatorInternalTargets.RunProjection := by
 intro R body alpha Delta packed parameter count initial final work results value hf hi hr hp hh
 let xs : Fin 2 → OTerm alpha := Fin.cons packed (Fin.cons parameter Fin.elim0)
 have hc : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.completed R) final packed parameter)) :=
   binaryValue (OriginalHereditaryRuntimeIterationDefinitions.run R)
     OriginalHereditaryEvaluatorDefinitions.computedFuel OriginalHereditaryEvaluatorDefinitions.initial
     final count initial xs hr hf hi
 have hs := unaryValue InternalUnpair.right (OriginalHereditaryEvaluatorDefinitions.completed R)
   results final xs (pairRight final work results hp) hc
 exact unaryValue InternalListCodec.headCode
   (rightOf (OriginalHereditaryEvaluatorDefinitions.completed R)) value results xs hh hs

theorem emptyWorkStep (R : Program 2) (state results : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state z results))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) state state)) := by
 unfold OriginalHereditaryCombinedStep.step
 apply InternalAcceptanceBranchProof.zeroBranchIntro
 exact pairLeft state z results hp
 exact projectionValue 0 (Fin.cons state Fin.elim0)

theorem emptyWorkIteration : OriginalHereditaryEvaluatorInternalTargets.EmptyWorkIteration := by
 intro R body alpha Delta state results count hp
 exact InternalNumericIterationFixedPointProof.fixedValue (OriginalHereditaryCombinedStep.step R)
   count state (emptyWorkStep R state results hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorInternalProof
