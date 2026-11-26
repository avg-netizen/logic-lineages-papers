module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermCodecProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem jobGraph (job typed typ rawJob raw parameter packed : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.job job packed parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![packed,parameter]
 have htyp := unaryValue InternalUnpair.left (.projection 0) typ packed xs (pairLeft packed typ raw hp) (projectionValue 0 xs)
 have hraw := unaryValue InternalUnpair.right (.projection 0) raw packed xs (pairRight packed typ raw hp) (projectionValue 0 xs)
 have hrawJob := binaryValue InternalPairing.pairing (rightOf (.projection 0)) (.projection 1) rawJob raw parameter xs hr hraw (projectionValue 1 xs)
 have htyped := binaryValue InternalPairing.pairing (leftOf (.projection 0)) (pairOf (rightOf (.projection 0)) (.projection 1)) typed typ rawJob xs ht htyp hrawJob
 exact binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) _ job (numeral 0) typed xs hj
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xs) htyped

theorem observedValue (Q : Program 2) (job typed typ rawJob raw parameter packed value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hv : Nonempty (Derivation body Delta (graph2 Q value packed parameter))) :
 Nonempty (Derivation body Delta (graph1 (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q) value job)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 have hrole := unaryValue InternalUnpair.left (.projection 0) (numeral 0) job xs (pairLeft job (numeral 0) typed hj) (projectionValue 0 xs)
 have htyped := unaryValue InternalUnpair.right (.projection 0) typed job xs (pairRight job (numeral 0) typed hj) (projectionValue 0 xs)
 have htype := unaryValue InternalUnpair.left (rightOf (.projection 0)) typ typed xs (pairLeft typed typ rawJob ht) htyped
 have hrawJob := unaryValue InternalUnpair.right (rightOf (.projection 0)) rawJob typed xs (pairRight typed typ rawJob ht) htyped
 have hraw := unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) raw rawJob xs (pairLeft rawJob raw parameter hr) hrawJob
 have hparam := unaryValue InternalUnpair.right (rightOf (rightOf (.projection 0))) parameter rawJob xs (pairRight rawJob raw parameter hr) hrawJob
 have hpacked := binaryValue InternalPairing.pairing SixSol20261112.Context.ScheduledDeletionDefinitions.jobType SixSol20261112.Context.ScheduledDeletionDefinitions.jobRaw packed typ raw xs hp htype hraw
 have hscalar := binaryValue Q SixSol20261112.Context.ScheduledDeletionDefinitions.jobPacked SixSol20261112.Context.ScheduledDeletionDefinitions.jobParameter value packed parameter xs hv hpacked hparam
 exact InternalAcceptanceBranchProof.zeroBranchIntro (leftOf (.projection 0)) (SixSol20261112.Context.ScheduledDeletionDefinitions.scalarFromJob Q)
   (.composition (OriginalTypedArgumentObservations.argumentObservations Q) ![SixSol20261112.Context.ScheduledDeletionDefinitions.jobRaw,SixSol20261112.Context.ScheduledDeletionDefinitions.jobParameter]) value xs hrole hscalar

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermCodecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermCodecProof
