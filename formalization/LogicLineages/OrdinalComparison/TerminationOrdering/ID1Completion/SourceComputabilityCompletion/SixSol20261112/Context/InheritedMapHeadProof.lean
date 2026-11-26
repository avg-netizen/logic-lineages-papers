module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.RawDeletionMapCellProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapHeadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel eqn eqnRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalRecursionClosureLogicProof (closedApply)
open InheritedMapDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalPairing.pairing InternalUnpair.left
  InternalUnpair.right InternalListMap.map

theorem atPairs (Q : Program 2)
    (rawJob typ annotated typed raw parameter packed scalar rawScalar : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotated z typed)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (ScheduledDeletionDefinitions.scalarFromJob Q) scalar annotated)))
    (hv : Nonempty (Derivation body Delta (graph2 (DeletionMapDefinitions.rawScalarFromJob Q) rawScalar rawJob typ))) :
    Nonempty (Derivation body Delta (eqn scalar rawScalar)) := by
  have left := ScheduledDeletionSupportProof.scalarAtPairs Q annotated z typed typ rawJob raw parameter packed scalar
    ha ht hr hp hs
  have right := RawDeletionMapCellProof.scalarAtPairs Q rawJob typ raw parameter packed rawScalar hr hp hv
  exact valueUnique Q scalar rawScalar ![packed,parameter] left right

/-- The actual head equality is derived from the literal shell and both actual
Q calls. Raw-job coordinates and real outer-type repacking are queried inside. -/
theorem actualHead (Q : Program 2) (rawJob typ annotated scalar rawScalar : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 inheritedJob annotated rawJob typ)))
    (hs : Nonempty (Derivation body Delta (graph1 (ScheduledDeletionDefinitions.scalarFromJob Q) scalar annotated)))
    (hv : Nonempty (Derivation body Delta (graph2 (DeletionMapDefinitions.rawScalarFromJob Q) rawScalar rawJob typ))) :
    Nonempty (Derivation body Delta (eqn scalar rawScalar)) := by
  let typed : Program 2 := pairOf (.projection 1) (.projection 0)
  let raw : Program 2 := leftOf (.projection 0)
  let parameter : Program 2 := rightOf (.projection 0)
  let packed : Program 2 := pairOf (.projection 1) raw
  let qs : Fin 4 → Program 2 := ![typed,raw,parameter,packed]
  let xs : Fin 2 → OTerm alpha := ![rawJob,typ]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [eqnRelabel]
  let xx : Fin 2 → OTerm beta := ![rawJob.relabel j,typ.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
    · rfl
    · rfl
  rw [hx] at hq
  have qt : Nonempty (Derivation body Theta (programGraph typed (ys 0) xx)) := hq 0
  have qr : Nonempty (Derivation body Theta (programGraph raw (ys 1) xx)) := hq 1
  have qp : Nonempty (Derivation body Theta (programGraph parameter (ys 2) xx)) := hq 2
  have qv : Nonempty (Derivation body Theta (programGraph packed (ys 3) xx)) := hq 3
  have ha' := renameInto ha j Theta hj
  have hs' := renameInto hs j Theta hj
  have hv' := renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename] at ha' hs' hv'
  have ht := binaryRecover InternalPairing.pairing (.projection 1) (.projection 0)
    (ys 0) (typ.relabel j) (rawJob.relabel j) xx qt (projectionValue 1 xx) (projectionValue 0 xx)
  have haPair := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) typed
    (annotated.relabel j) z (ys 0) xx ha' (constantValue 0 xx) qt
  have hl := unaryRecover InternalUnpair.left (.projection 0) (ys 1) (rawJob.relabel j) xx qr (projectionValue 0 xx)
  have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 2) (rawJob.relabel j) xx qp (projectionValue 0 xx)
  have hraw := closedApply
    (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body beta (rawJob.relabel j) (ys 1) (ys 2))
    (andIntro hl hr)
  have hpacked := binaryRecover InternalPairing.pairing (.projection 1) raw
    (ys 3) (typ.relabel j) (ys 1) xx qv (projectionValue 1 xx) qr
  exact atPairs Q (rawJob.relabel j) (typ.relabel j) (annotated.relabel j) (ys 0)
    (ys 1) (ys 2) (ys 3) (scalar.relabel j) (rawScalar.relabel j) haPair ht hraw hpacked hs' hv'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapHeadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapHeadProof
