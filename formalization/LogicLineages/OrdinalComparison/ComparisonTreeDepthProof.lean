module
public import LogicLineages.OrdinalComparison.ComparisonTreeFrontierProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree

private theorem search_primitive : Primrec (fun p : (Nat × Nat) × Nat =>
    decide (encodedComparisonFrontier p.1 p.2=[])) :=
  (Primrec.eq.comp frontier_program.2.1 (Primrec.const [])).decide

theorem partial_recursive : Partrec encodedComparisonDepthPartial :=
  Partrec.rfind search_primitive.to_comp.partrec.to₂

theorem total (root : Nat × Nat) : (encodedComparisonDepthPartial root).Dom := by
  obtain ⟨depth,hd⟩ := terminates root
  apply Nat.rfind_dom.mpr
  refine ⟨depth,Part.mem_some_iff.mpr ?_,?_⟩
  · simp only [hd,decide_true]
  · intro m hm
    exact True.intro

private theorem depth_mem (root : Nat × Nat) :
    encodedComparisonTreeDepth root∈encodedComparisonDepthPartial root := by
  classical
  unfold encodedComparisonTreeDepth
  rw [Part.getOrElse_of_dom _ (total root) 0]
  exact Part.get_mem (total root)

theorem depth_computable : Computable encodedComparisonTreeDepth :=
  partial_recursive.of_eq_tot depth_mem

theorem depth_closed (root : Nat × Nat) :
    encodedComparisonFrontier root (encodedComparisonTreeDepth root)=[] := by
  have hs := Nat.rfind_spec (depth_mem root)
  exact decide_eq_true_eq.mp (Part.mem_some_iff.mp hs).symm

theorem depth_minimal (root : Nat × Nat) (k : Nat) (hk : k<encodedComparisonTreeDepth root) :
    encodedComparisonFrontier root k≠[] := by
  have hs := Nat.rfind_min (depth_mem root) hk
  have hf : decide (encodedComparisonFrontier root k=[])=false := (Part.mem_some_iff.mp hs).symm
  intro hz
  simp only [hz,decide_true] at hf
  contradiction

theorem depth_program : Targets.ActualComparisonDepthProgram := by
  refine ⟨partial_recursive,total,depth_computable,?_⟩
  intro root
  have hp : 1≤encodedComparisonTreeDepth root := by
    have hn : encodedComparisonTreeDepth root≠0 := by
      intro hz
      have hc := depth_closed root
      rw [hz] at hc
      cases hc
    omega
  exact ⟨hp,depth_closed root,fun k hk => depth_minimal root k hk⟩

end LogicLineages.OrdinalComparison.ComparisonTree
