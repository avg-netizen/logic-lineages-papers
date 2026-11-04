module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentPreservationProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Proof
open ExistentialPlan PrimitiveLowering SourceGroundBinderFragment

theorem graph_fragment {Γ} (e : Expr Γ) : Fragment e.graph.term := by
  rw [(PrimitiveLowering.Proof.primitiveRealization Γ e).1]
  exact SourceGroundBinderFragment.Proof.primitiveExpressions Γ e

theorem generated_fragment {Γ} (g : Gate Γ) :
    ∀ f ∈ forest g, Fragment f.1.term ∧ Fragment f.2.term := by
  intro f hf
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hf
  exact ⟨graph_fragment e.1,graph_fragment e.2⟩

theorem compilerPreservation : Targets.CompilerPreservation := by
  intro Γ q
  induction q with
  | done => intro h f hf; cases hf
  | equation a b q ih =>
    rintro ⟨ha,hb,hq⟩ f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨dag_rename _ a ha,dag_rename _ b hb⟩
    · exact ih hq f hf
  | gate g q ih =>
    intro h f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact generated_fragment _ f hf
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hf
      have hh := ih h e he
      exact ⟨dag_rename _ e.1 hh.1,dag_rename _ e.2 hh.2⟩
  | existsGround q ih => exact ih
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Proof
