module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedObservationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedObservationHeadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.MapAppendCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedObservationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (refl symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionClosureLogicProof (closedApply)
open OriginalContextInsertionSupportProof (binaryInputs)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open SixSol20261112.Context
open InheritedMapDefinitions InheritedObservationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map InternalListCodec.consCode

theorem unaryMapZero (F : Program 1) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) z z)) := by
  obtain ⟨law⟩ := InternalListMapProof.actualOriginalListMapZero body 0 F alpha z Fin.elim0
  have hr : Nonempty (Derivation body Delta (equal z z)) := by
    rw [equalEqn]
    exact ⟨refl z⟩
  exact closedApply ⟨Derivation.conjunctionRight law⟩ hr

theorem zeroCore (Q : Program 2) (typ annotated valueRow : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields Q z typ annotated valueRow))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow z typ)) := by
  let A := InternalListMap.map (k := 1) inheritedJob
  let S := InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)
  let M := InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)
  have ha := valueUnique A annotated z ![z,typ] (andLeft hf) (MapAppendCoreProof.mapZero inheritedJob typ)
  have hs := headTransport S valueRow annotated z Fin.elim0 ha (andRight hf)
  obtain ⟨he⟩ := valueUnique S valueRow z ![z] hs (unaryMapZero (ChildContentDefinitions.observationFromJob Q))
  exact outputTransport M z valueRow ![z,typ] ⟨symm he⟩
    (MapAppendCoreProof.mapZero (DeletionMapDefinitions.rawScalarFromJob Q) typ)

theorem consAtValues (Q : Program 2)
    (code head tail typ annotated valueRow annotatedHead annotatedTail scalarHead scalarTail rawHead : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row Q tail)))
    (hf : Nonempty (Derivation body Delta (fields Q code typ annotated valueRow)))
    (hh : Nonempty (Derivation body Delta (graph2 inheritedJob annotatedHead head typ)))
    (ht : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) inheritedJob) annotatedTail tail typ)))
    (hs : Nonempty (Derivation body Delta (graph1 (ChildContentDefinitions.observationFromJob Q) scalarHead annotatedHead)))
    (hu : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) scalarTail annotatedTail)))
    (hv : Nonempty (Derivation body Delta (graph2 (DeletionMapDefinitions.rawScalarFromJob Q) rawHead head typ))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow code typ)) := by
  have hannotated := InternalListMapProof.consForward inheritedJob code head tail annotatedHead annotatedTail annotated
    (Fin.cons typ Fin.elim0) hc hh ht (andLeft hf)
  have hrow := InternalListMapProof.consForward (ChildContentDefinitions.observationFromJob Q)
    annotated annotatedHead annotatedTail scalarHead scalarTail valueRow Fin.elim0 hannotated hs hu (andRight hf)
  have he := InheritedObservationHeadProof.actualHead Q head typ annotatedHead scalarHead rawHead hh hs hv
  have hrow' := binaryInputs InternalListCodec.consCode valueRow scalarHead scalarTail rawHead scalarTail
    he ⟨refl scalarTail⟩ hrow
  have htail := rowApply Q tail typ annotatedTail scalarTail hi (andIntro ht hu)
  exact InternalListMapProof.consBackward (DeletionMapDefinitions.rawScalarFromJob Q)
    code head tail rawHead scalarTail valueRow (Fin.cons typ Fin.elim0) hc hv htail hrow'

theorem consCore (Q : Program 2) (code head tail typ annotated valueRow : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row Q tail)))
    (hf : Nonempty (Derivation body Delta (fields Q code typ annotated valueRow))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow code typ)) := by
  let h : Program 3 := .composition inheritedJob ![.projection 0,.projection 2]
  let t : Program 3 := .composition (InternalListMap.map (k := 1) inheritedJob) ![.projection 1,.projection 2]
  let s : Program 3 := .composition (ChildContentDefinitions.observationFromJob Q) (fun _ : Fin 1 => h)
  let u : Program 3 := .composition (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) (fun _ : Fin 1 => t)
  let v : Program 3 := .composition (DeletionMapDefinitions.rawScalarFromJob Q) ![.projection 0,.projection 2]
  let qs : Fin 5 → Program 3 := ![h,t,s,u,v]
  let xs : Fin 3 → OTerm alpha := ![head,tail,typ]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename]
  let xx : Fin 3 → OTerm beta := ![head.relabel j,tail.relabel j,typ.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
    · rfl
    · rfl
    · rfl
  rw [hx] at hq
  have qh : Nonempty (Derivation body Theta (programGraph h (ys 0) xx)) := hq 0
  have qt : Nonempty (Derivation body Theta (programGraph t (ys 1) xx)) := hq 1
  have qs : Nonempty (Derivation body Theta (programGraph s (ys 2) xx)) := hq 2
  have qu : Nonempty (Derivation body Theta (programGraph u (ys 3) xx)) := hq 3
  have qv : Nonempty (Derivation body Theta (programGraph v (ys 4) xx)) := hq 4
  have hh := binaryRecover inheritedJob (.projection 0) (.projection 2)
    (ys 0) (head.relabel j) (typ.relabel j) xx qh (projectionValue 0 xx) (projectionValue 2 xx)
  have ht := binaryRecover (InternalListMap.map (k := 1) inheritedJob) (.projection 1) (.projection 2)
    (ys 1) (tail.relabel j) (typ.relabel j) xx qt (projectionValue 1 xx) (projectionValue 2 xx)
  have hs := unaryRecover (ChildContentDefinitions.observationFromJob Q) h (ys 2) (ys 0) xx qs qh
  have hu := unaryRecover (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) t
    (ys 3) (ys 1) xx qu qt
  have hv := binaryRecover (DeletionMapDefinitions.rawScalarFromJob Q) (.projection 0) (.projection 2)
    (ys 4) (head.relabel j) (typ.relabel j) xx qv (projectionValue 0 xx) (projectionValue 2 xx)
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hi' := renameInto hi j Theta hj
  rw [InheritedObservationSyntaxProof.rowRename] at hi'
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  exact consAtValues Q (code.relabel j) (head.relabel j) (tail.relabel j) (typ.relabel j)
    (annotated.relabel j) (valueRow.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    hc' hi' hf' hh ht hs hu hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedObservationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedObservationCoreProof
