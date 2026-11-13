module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalPreservationInductionDefinitions
open EvaluatorKeyCanonicalInductionDefinitions (C)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open EvaluatorKeyCanonicalPreservationSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalSquareRootArithmeticSupportProof (orderRight)
open SourceComputabilityFormulaSupportProof (numeral)
theorem atTag (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : EvaluatorKeyCanonicalPreservationDefinitions.Compatible p H G W)
 (q input out parameter : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) input))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases input parameter _ ht
 intro beta j Theta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal
 rw [resultRename]
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hr' := renameInto hraw j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 rw [graph1Rename] at hr'
 obtain ⟨eq⟩ := valueUnique InternalUnpair.right payload (q.relabel j) (![input.relabel j]) hpr hr'
 obtain ⟨fl⟩ := hfl
 obtain ⟨al⟩ := hal
 exact EvaluatorKeyCanonicalPreservationApplicationQueriesProof.withOutputs p H G W P compat
  (q.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j) arrow d e fp ap fn arg
  hb' hp' hc ⟨orderRight fp eq fl⟩ ⟨orderRight ap eq al⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationProof
