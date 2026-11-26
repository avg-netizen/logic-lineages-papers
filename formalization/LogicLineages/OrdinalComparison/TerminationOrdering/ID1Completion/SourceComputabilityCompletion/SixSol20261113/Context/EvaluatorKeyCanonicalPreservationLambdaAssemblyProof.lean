module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaContextProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut
open EvaluatorKeyCanonicalInductionDefinitions (C)
open EvaluatorKeyCanonicalPreservationInductionDefinitions EvaluatorKeyCanonicalPreservationDefinitions
open EvaluatorKeyCanonicalPreservationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atCoordinates (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : Compatible p H G W)
 (q input out parameter d e child arrow childParameter childPayload childOut c gamma childGamma : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields input d e child arrow)))
 (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter childParameter)))
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
 (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q)))
 (hc : Nonempty (Derivation body Delta (graph2 (C p H G W P) childOut child childParameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hcons : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma d gamma))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 have ready := EvaluatorKeyCanonicalPreservationLambdaCoreProof.atOutput p H G W P
   q input out parameter d e child childParameter childPayload childOut hb hp hf hr hlt hc
 have hl := EvaluatorKeyDomainClosureSupportProof.factors p H G W input parameter (andLeft hp)
 have hright := EvaluatorKeyDomainClosureSupportProof.factors p H G W out parameter ready.2.1
 have hinput := EvaluatorKeyCanonicalPreservationLambdaSupportProof.inputConstructor input d e child arrow hsf
 have ht := OriginalLambdaTraversalLambdaSelectorProof.bodyType input e child
   (andLeft (andRight (andRight hf))) (andLeft (andRight (andRight (andRight hf))))
 have hcp := OriginalPositionStructuralKeyLambdaContextProof.childPair input d e child parameter childParameter
   c gamma childGamma hf hparam hcons
 have ha := SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof.actualLambda
   (baseRepresentative p H G W) H G (member p H G W) W compat body alpha Delta
   input out child childOut d e parameter childParameter c gamma childGamma
   (andRight hl) (andRight hright) hparam hcons hcp hinput ready.2.2.1 ht ready.2.2.2 ready.1
 exact andIntro ready.2.1 (andRight (andRight ha))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaAssemblyProof
