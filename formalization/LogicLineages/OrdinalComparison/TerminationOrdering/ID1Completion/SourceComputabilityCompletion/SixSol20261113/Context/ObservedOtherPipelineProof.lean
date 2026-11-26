module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineGenericProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem conditionFromDomain (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W input parameter))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalRankGuardedLeafTupleProof.condition (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W)
   (suc z) input parameter)) := by
 let q := OriginalClassContextAllPositionSelection.inputs p H G W P
 have hf := conjunctionRecover (BottomRepresentative.windowAt p.window)
   (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource
   (Fin.cons input (Fin.cons parameter Fin.elim0)) (andRight hd)
 have hv := iffBackward (OriginalRankGuardedLeafTupleProof.priorSourceIff q H G W (suc z) input parameter) (andRight hf)
 rw [OriginalRankGuardedLeafTupleProof.conditionProgram]
 exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) (andLeft hf) hv

def observers : Fin 6 → Program 1 := ![OriginalRawSyntaxTransport.variableRankPackedRaw,
 OriginalFunctionNeutrality.mark,OriginalConstructorShape.mark,OriginalVariableRepresentative.variableMark,
 BottomSpineMeasure.measure,BottomRepresentative.bottomTest]
/-- All five sidecar guard acceptances are derived at the actual minimum.
The marks are merely actual query outputs, not desired equalities. -/
theorem priorValueAtMarks (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output parameter : OTerm alpha) (marks : Fin 6 → OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P).base.oldRepresentative output input parameter)))
 (hmarks : ∀ i, Nonempty (Derivation body Delta (graph1 (observers i) (marks i) input))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalRankGuardedLeaf.priorData (OriginalClassContextAllPositionSelection.inputs
     (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P) H G W).oldRepresentative output input parameter)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 let m := OriginalClassContextAllPositionSelection.inputs q H G W P
 let raw := OriginalRankGuardedLeafTupleProof.rawData m H G W
 let window := (OriginalRankGuardedLeaf.refined m H G W).window
 let active := OriginalFunctionNeutrality.active raw window
 have hactive : Nonempty (Derivation body Delta (graph2 active (suc z) input parameter)) :=
   conditionFromDomain q H G W P input parameter hd
 have hh := OriginalAllPositionMinimumSupportProof.minimumHit q H G W P input output parameter hd hm
 have hraw := ObservedOtherGuardProof.initialValue q H G W P input output parameter (marks 0) hd hm (hmarks 0)
 exact ObservedOtherPipelineGenericProof.pipeline raw window input output parameter marks hactive hraw
   hmarks (fun i => ObservedOtherMarksProof.acceptedMarks p H G W P input output parameter (marks i) hd hh)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineProof
