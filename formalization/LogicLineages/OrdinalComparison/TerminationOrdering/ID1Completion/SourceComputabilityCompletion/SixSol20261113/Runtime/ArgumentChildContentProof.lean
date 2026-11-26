module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedMapSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermCodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentChildContentProof
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
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalTagArithmeticSyntaxProof (z)
attribute [local irreducible] programGraph
theorem cons (Q : Program 2) (raw domain child tailRaw parameter rawJobs annotatedPrefix childRow first second returned : OTerm alpha)
 (hcon : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain child tailRaw)))
 (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
 (hs : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 2) (numeral 1) z raw rawJobs)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q)) childRow annotatedPrefix)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (numeral 2) childRow)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z childRow)))
 (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) childRow)))
 (hr : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons returned raw first second))) :
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) returned raw parameter)) := by
 apply SixSol20261113.Context.AdmittedMapSlotsProof.binaryCases
   (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q) annotatedPrefix childRow first second _
   (SixSol20261113.Runtime.SourceFramedScanLengthProof.scanLength (numeral 2) (numeral 1) z raw rawJobs annotatedPrefix hs) hm hf hsecond
 intro beta j Theta tail hi hc ht
 have hcon' := renameInto hcon j Theta hi
 have he' := renameInto he j Theta hi
 have hs' := renameInto hs j Theta hi
 have hm' := renameInto hm j Theta hi
 have hr' := renameInto hr j Theta hi
 simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,numeralRename,InternalTagArithmeticSyntaxProof.zRelabel] at hcon' he' hs' hm' hr'
 rw [graph2Rename]
 exact SixSol20261113.Context.ChildConsProof.actual Q body beta Theta (raw.relabel j) (domain.relabel j) (child.relabel j) (tailRaw.relabel j) (parameter.relabel j) (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) (first.relabel j) tail (second.relabel j) (returned.relabel j) hcon' he' hs' hm' hc ht hr'

theorem observed (Q : Program 2) (job typed rawJob raw parameter value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed z rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) value raw parameter))) :
 Nonempty (Derivation body Delta (graph1 (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q) value job)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 have hrole := unaryValue InternalUnpair.left (.projection 0) (numeral 1) job xs (pairLeft job (numeral 1) typed hj) (projectionValue 0 xs)
 have htyped := unaryValue InternalUnpair.right (.projection 0) typed job xs (pairRight job (numeral 1) typed hj) (projectionValue 0 xs)
 have hrawJob := unaryValue InternalUnpair.right (rightOf (.projection 0)) rawJob typed xs (pairRight typed z rawJob ht) htyped
 have hraw := unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) raw rawJob xs (pairLeft rawJob raw parameter hr) hrawJob
 have hparam := unaryValue InternalUnpair.right (rightOf (rightOf (.projection 0))) parameter rawJob xs (pairRight rawJob raw parameter hr) hrawJob
 have hargs := binaryValue (OriginalTypedArgumentObservations.argumentObservations Q) SixSol20261112.Context.ScheduledDeletionDefinitions.jobRaw SixSol20261112.Context.ScheduledDeletionDefinitions.jobParameter value raw parameter xs hv hraw hparam
 exact InternalAcceptanceBranchProof.successorBranchIntro (leftOf (.projection 0)) (SixSol20261112.Context.ScheduledDeletionDefinitions.scalarFromJob Q)
   (.composition (OriginalTypedArgumentObservations.argumentObservations Q) ![SixSol20261112.Context.ScheduledDeletionDefinitions.jobRaw,SixSol20261112.Context.ScheduledDeletionDefinitions.jobParameter]) value z xs hrole hargs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentChildContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentChildContentProof
