module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionTargets
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGValidationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open Operations

theorem application_raw_exact {Γ σ τ} (f : Input Γ (.arrow σ τ)) (a : Input Γ σ) :
    applicationRaw (SyntaxCode.typeCode τ) (encode ⟨Γ,.arrow σ τ,f⟩) (encode ⟨Γ,σ,a⟩) =
      encode ⟨Γ,τ,ScopedDAG.application f a⟩ := by
  simp [applicationRaw,rawNode,encode,ScopedDAG.application,encodeGraph,node,
    append_graph,front_index,back_index,graph_length,referenceIndex]

theorem eraser_raw_exact {Γ} (a b : Input Γ .ground) :
    eraserRaw (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) =
      encode ⟨Γ,.ground,ScopedDAG.eraser a b⟩ := by
  simp [eraserRaw,rawNode,encode,ScopedDAG.eraser,encodeGraph,node,
    append_graph,insert_graph,front_index,back_index,map_index,graph_length,
    referenceIndex,SyntaxCode.typeCode,Nat.add_comm]
  exact ((back_index b.specs (a.root.map insertSpec)).trans
    (congrArg (fun n => b.specs.length+n) (map_index a.root))).symm

theorem application_typed {Γ σ τ} (f : Input Γ (.arrow σ τ)) (a : Input Γ σ) :
    application (SyntaxCode.typeCode τ) (encode ⟨Γ,.arrow σ τ,f⟩) (encode ⟨Γ,σ,a⟩) =
      some (encode ⟨Γ,τ,ScopedDAG.application f a⟩) := by
  have hguard : applicationGuard (SyntaxCode.typeCode τ)
      (encode ⟨Γ,.arrow σ τ,f⟩) (encode ⟨Γ,σ,a⟩) = true := by
    simp only [applicationGuard,typedAccepted]
    simp [encode,SyntaxCode.typeCode]
  simp [application,hguard,application_raw_exact]

theorem eraser_typed {Γ} (a b : Input Γ .ground) :
    eraser (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) =
      some (encode ⟨Γ,.ground,ScopedDAG.eraser a b⟩) := by
  have hguard : eraserGuard (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) = true := by
    simp only [eraserGuard,typedAccepted]
    simp [encode,SyntaxCode.typeCode]
  simp [eraser,hguard,eraser_raw_exact]

theorem typedExactness : RawCheckedCompositionTargets.TypedExactness :=
  ⟨fun _ _ _ f a => application_typed f a,fun _ a b => eraser_typed a b⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
