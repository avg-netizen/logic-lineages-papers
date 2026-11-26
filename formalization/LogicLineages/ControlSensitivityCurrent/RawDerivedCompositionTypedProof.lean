module
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionTargets
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionTypedProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open Operations CheckedComposition

theorem detector_left_raw {Γ} (a b : Input Γ .ground) :
    detectorLeftRaw (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) =
      encode ⟨Γ,.ground,ScopedDAG.detectorLeft a b⟩ := by
  simp only [detectorLeftRaw,eraser_raw_exact,ScopedDAG.detectorLeft]

theorem detector_right_raw {Γ} (a b : Input Γ .ground) :
    detectorRightRaw (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) =
      encode ⟨Γ,.ground,ScopedDAG.detectorRight a b⟩ := by
  simp only [detectorRightRaw,eraser_raw_exact,ScopedDAG.detectorRight]

theorem eraser_guard_typed {Γ} (a b : Input Γ .ground) :
    eraserGuard (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) = true := by
  simp only [eraserGuard,typedAccepted]
  simp [encode,SyntaxCode.typeCode]

theorem detectors_typed {Γ} (a b : Input Γ .ground) :
    detectors (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) = some
      (encode ⟨Γ,.ground,ScopedDAG.detectorLeft a b⟩,
       encode ⟨Γ,.ground,ScopedDAG.detectorRight a b⟩) := by
  simp [detectors,eraser_guard_typed,detector_left_raw,detector_right_raw]

theorem zero_raw (Γ : List Ty) : zeroRaw (Γ.map SyntaxCode.typeCode) =
    encode ⟨Γ,.ground,ScopedDAG.zero Γ⟩ := by
  rfl

theorem aggregate_raw {Γ} (es : List (Input Γ .ground × Input Γ .ground)) :
    aggregateRaw (Γ.map SyntaxCode.typeCode)
      (es.map (fun p => (encode ⟨Γ,.ground,p.1⟩,encode ⟨Γ,.ground,p.2⟩))) =
      (encode ⟨Γ,.ground,(ScopedDAG.aggregate es).1⟩,
       encode ⟨Γ,.ground,(ScopedDAG.aggregate es).2⟩) := by
  induction es with
  | nil => simp [aggregateRaw,ScopedDAG.aggregate,zero_raw]
  | cons p es ih =>
      rcases p with ⟨a,b⟩
      simp only [List.map_cons,aggregateRaw,ih,detector_left_raw,detector_right_raw,
        eraser_raw_exact,ScopedDAG.aggregate]

theorem aggregate_guard_typed {Γ} (es : List (Input Γ .ground × Input Γ .ground)) :
    aggregateGuard (Γ.map SyntaxCode.typeCode)
      (es.map (fun p => (encode ⟨Γ,.ground,p.1⟩,encode ⟨Γ,.ground,p.2⟩))) = true := by
  induction es with
  | nil => rfl
  | cons p es ih =>
      rw [List.map_cons]
      change (eraserGuard (encode ⟨Γ,.ground,p.1⟩) (encode ⟨Γ,.ground,p.2⟩) &&
        decide ((encode ⟨Γ,.ground,p.1⟩).1 = Γ.map SyntaxCode.typeCode) &&
        aggregateGuard (Γ.map SyntaxCode.typeCode)
          (es.map (fun q => (encode ⟨Γ,.ground,q.1⟩,encode ⟨Γ,.ground,q.2⟩)))) = true
      rw [eraser_guard_typed, ih]
      simp [encode]

theorem aggregate_typed {Γ} (es : List (Input Γ .ground × Input Γ .ground)) :
    aggregate (Γ.map SyntaxCode.typeCode)
      (es.map (fun p => (encode ⟨Γ,.ground,p.1⟩,encode ⟨Γ,.ground,p.2⟩))) = some
      (encode ⟨Γ,.ground,(ScopedDAG.aggregate es).1⟩,
       encode ⟨Γ,.ground,(ScopedDAG.aggregate es).2⟩) := by
  simp only [aggregate,aggregate_guard_typed,ite_true,aggregate_raw]

theorem magnify_raw {Γ} (a : Input Γ .ground) :
    magnifyRaw (encode ⟨Γ,.ground,a⟩) = encode ⟨Γ,.ground,magnifyInput a⟩ := by
  simp [magnifyRaw,magnifyInput,encode,encodeGraph,node,CheckedComposition.rawNode,
    insert_graph,referenceIndex,SyntaxCode.typeCode]
  exact (map_index a.root).symm

theorem identity_raw {Γ} (a : Input Γ .ground) :
    identityRaw (encode ⟨Γ,.ground,a⟩) = encode ⟨Γ,.ground,identityInput a⟩ := by
  simp [identityRaw,identityInput,encode,encodeGraph,node,CheckedComposition.rawNode,
    referenceIndex,variableIndex,SyntaxCode.typeCode] <;> omega

theorem constant_raw {Γ} (a : Input Γ .ground) :
    constantRaw (encode ⟨Γ,.ground,a⟩) = encode ⟨Γ,.ground,constantInput a⟩ := by
  simp [constantRaw,constantInput,encode,encodeGraph,node,CheckedComposition.rawNode,
    referenceIndex,SyntaxCode.typeCode] <;> omega

theorem wrapper_raw {Γ} (a : Input Γ .ground) (upper : Bool) :
    wrapperRaw upper (encode ⟨Γ,.ground,a⟩) =
      encode ⟨Γ,.ground,if upper then upperInput a else lowerInput a⟩ := by
  cases upper <;> simp [wrapperRaw,magnify_raw,identity_raw,constant_raw,
    lowerInput,upperInput]

theorem wrap_typed {Γ} (a : Input Γ .ground) (upper : Bool) :
    wrap upper (encode ⟨Γ,.ground,a⟩) = some
      (encode ⟨Γ,.ground,if upper then upperInput a else lowerInput a⟩) := by
  have hg : wrapperGuard (encode ⟨Γ,.ground,a⟩) = true := by
    simp only [wrapperGuard,typedAccepted]
    rfl
  simp only [wrap,hg,ite_true,wrapper_raw]

theorem typedExactness : RawDerivedCompositionTargets.TypedExactness :=
  ⟨fun _ a b => detectors_typed a b,fun _ es => aggregate_typed es,
    fun _ a upper => wrap_typed a upper⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
