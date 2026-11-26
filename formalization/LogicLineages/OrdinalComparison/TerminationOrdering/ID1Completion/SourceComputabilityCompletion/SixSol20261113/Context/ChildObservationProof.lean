module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261112.Context.ScheduledDeletionDefinitions ChildContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem termValue (Q : Program 2) (job typed typ rawJob raw parameter packed value : OTerm alpha)
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hv : Nonempty (Derivation body Delta (graph1 (observationFromJob Q) value job))) :
    Nonempty (Derivation body Delta (graph2 Q value packed parameter)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
  have hrole := unaryValue InternalUnpair.left (.projection 0) z job xs
    (pairLeft job z typed hj) (projectionValue 0 xs)
  have hs := InternalAcceptanceBranchProof.zeroBranchElim (leftOf (.projection 0)) (scalarFromJob Q)
    (.composition (OriginalTypedArgumentObservations.argumentObservations Q) ![jobRaw,jobParameter])
    value xs hrole hv
  exact SixSol20261112.Context.ScheduledDeletionSupportProof.scalarAtPairs Q job z typed typ rawJob raw parameter packed value hj ht hr hp hs

theorem argumentsValue (Q : Program 2) (job typed typ rawJob raw parameter value : OTerm alpha)
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (hv : Nonempty (Derivation body Delta (graph1 (observationFromJob Q) value job))) :
    Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) value raw parameter)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
  have hrole := unaryValue InternalUnpair.left (.projection 0) (numeral 1) job xs
    (pairLeft job (numeral 1) typed hj) (projectionValue 0 xs)
  have hs := InternalAcceptanceBranchProof.successorBranchElim (leftOf (.projection 0)) (scalarFromJob Q)
    (.composition (OriginalTypedArgumentObservations.argumentObservations Q) ![jobRaw,jobParameter])
    value z xs hrole hv
  have htyped := unaryValue InternalUnpair.right (.projection 0) typed job xs
    (pairRight job (numeral 1) typed hj) (projectionValue 0 xs)
  have hrawJob := unaryValue InternalUnpair.right (rightOf (.projection 0)) rawJob typed xs
    (pairRight typed typ rawJob ht) htyped
  have hraw := unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) raw rawJob xs
    (pairLeft rawJob raw parameter hr) hrawJob
  have hparameter := unaryValue InternalUnpair.right (rightOf (rightOf (.projection 0))) parameter rawJob xs
    (pairRight rawJob raw parameter hr) hrawJob
  exact binaryRecover (OriginalTypedArgumentObservations.argumentObservations Q) jobRaw jobParameter
    value raw parameter xs hs hraw hparameter
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
