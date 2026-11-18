module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsReferenceProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence

theorem append_graph {Γ ss tt} (a : DAG Γ ss) (b : DAG Γ tt) :
    encodeGraph (ScopedDAG.append a b) = appendTable (encodeGraph a) (encodeGraph b) := by
  induction b <;> simp_all [ScopedDAG.append,encodeGraph,appendTable,front_index]
theorem append : RawSourceDAGOperationsTargets.Append :=
  ⟨fun _ _ _ a b => append_graph a b,fun a b => by simp [appendTable,Nat.add_comm]⟩

theorem rename_graph {Γ Θ ss} (r : Renaming Γ Θ) (g : DAG Γ ss) :
    encodeGraph (ScopedDAG.rename r g) = renameTable (renamingCode r) (encodeGraph g) := by
  induction g <;> simp_all [ScopedDAG.rename,encodeGraph,renameTable,renameNode,node,prefix_index]
theorem rename_input {Γ Θ τ} (r : Renaming Γ Θ) (d : Input Γ τ) :
    encode ⟨Θ,τ,ScopedDAG.renameInput r d⟩ =
      renameCode (Θ.map SyntaxCode.typeCode) (renamingCode r) (encode ⟨Γ,τ,d⟩) := by
  simp [encode,ScopedDAG.renameInput,renameCode,rename_graph]
theorem rename : RawSourceDAGOperationsTargets.Rename :=
  ⟨fun _ _ r => renaming_length r,fun _ _ _ r g => rename_graph r g,
    fun _ _ _ r d => rename_input r d,fun ρ as => by simp [renameTable]⟩

theorem insert_graph {Γ ss} (g : DAG Γ ss) : encodeGraph g.insert = insertTable (encodeGraph g) := by
  induction g <;> simp_all [DAG.insert,encodeGraph,insertTable,insertNode,node,
    insertSpec,map_index,insertion_index,SyntaxCode.typeCode]
  case app ss Δ σ τ d f a ih => exact ⟨map_index f,map_index a⟩
  case lam ss Δ σ τ d b ih => exact map_index b
theorem insert : RawSourceDAGOperationsTargets.Insert :=
  ⟨fun _ _ g => insert_graph g,fun as => by simp [insertTable]⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations
