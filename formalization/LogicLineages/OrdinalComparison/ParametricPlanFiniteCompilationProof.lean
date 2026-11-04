module
public import LogicLineages.OrdinalComparison.ParametricPlanFiniteTargets
public import LogicLineages.OrdinalComparison.ParametricPrimitiveFiniteProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.Proof
open ExistentialPlan PrimitiveLowering ParametricPrimitiveFinite ParametricSourceEraser

theorem generatedLeaves : Targets.GeneratedLeaves := by
  intro G hm hi Γ g ρ e he
  obtain ⟨f,hf,he⟩ := List.mem_map.mp he
  subst e
  obtain ⟨hx,_⟩ := ParametricPrimitiveFinite.Proof.exactExpressionCalibration G hm hi (Block Γ) (inputs ρ) f.1
  obtain ⟨hy,_⟩ := ParametricPrimitiveFinite.Proof.exactExpressionCalibration G hm hi (Block Γ) (inputs ρ) f.2
  refine ⟨value G (inputs ρ) f.1+1,value G (inputs ρ) f.2+1,?_,?_⟩
  · rw [(PrimitiveLowering.Proof.primitiveRealization _ f.1).1]
    exact hx
  · rw [(PrimitiveLowering.Proof.primitiveRealization _ f.2).1]
    exact hy

theorem uniformCompiler : Targets.UniformCompiler := by
  intro G hm hi Γ q
  induction q with
  | done =>
    intro h ρ e he
    cases he
  | @equation Γ a b q ih =>
    intro h ρ e he
    change e ∈ (ScopedDAG.renameInput (compile q).embedding a,
      ScopedDAG.renameInput (compile q).embedding b)::(compile q).forest at he
    rcases List.mem_cons.mp he with rfl | he
    · let μ : Variable Γ .ground → Nat := fun x => ρ ((compile q).embedding x)
      obtain ⟨x,y,hx,hy⟩ := h.1 μ
      refine ⟨x,y,?_,?_⟩
      · exact (ParametricPrimitiveFinite.Proof.groundInputDAGRenaming G Γ _
          (compile q).embedding μ ρ (fun _ => rfl) a x).mpr hx
      · exact (ParametricPrimitiveFinite.Proof.groundInputDAGRenaming G Γ _
          (compile q).embedding μ ρ (fun _ => rfl) b y).mpr hy
    · exact ih h.2 ρ e he
  | @gate Γ g q ih =>
    intro h ρ e he
    change e ∈ forest (gateRename (compile q).embedding g) ++
      (compile q).forest.map (fun f => (ScopedDAG.renameInput (shift 9) f.1,
        ScopedDAG.renameInput (shift 9) f.2)) at he
    rcases List.mem_append.mp he with he | he
    · exact generatedLeaves G hm hi _ _ ρ e he
    · obtain ⟨f,hf,he⟩ := List.mem_map.mp he
      subst e
      let μ : Variable (compile q).context .ground → Nat := fun x => ρ (shift 9 x)
      obtain ⟨x,y,hx,hy⟩ := ih h μ f hf
      refine ⟨x,y,?_,?_⟩
      · exact (ParametricPrimitiveFinite.Proof.groundInputDAGRenaming G _ _ (shift 9)
          μ ρ (fun _ => rfl) f.1 x).mpr hx
      · exact (ParametricPrimitiveFinite.Proof.groundInputDAGRenaming G _ _ (shift 9)
          μ ρ (fun _ => rfl) f.2 y).mpr hy
  | @existsGround Γ q ih =>
    intro h ρ
    exact ih h ρ
end LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.Proof
