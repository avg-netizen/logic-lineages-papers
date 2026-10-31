module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
open GroundEquivalence PrimitiveLowering

theorem compilation : Targets.Compilation := by
  intro Γ q
  induction q with
  | done =>
    intro ρ
    constructor
    · intro _
      refine ⟨ρ,fun _ => rfl,?_⟩
      intro e he
      cases he
    · intro _
      trivial
  | @equation Γ a b q ih =>
    intro ρ
    simp only [Eval,compile,Result.Holds]
    constructor
    · rintro ⟨hab,hq⟩
      obtain ⟨ν,hν,he⟩ := (ih ρ).mp hq
      refine ⟨ν,hν,?_⟩
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (equation_dag_rename (compile q).embedding ρ ν hν a b).mpr hab
      · exact he e hm
    · rintro ⟨ν,hν,he⟩
      have hab := he (ScopedDAG.renameInput (compile q).embedding a,
        ScopedDAG.renameInput (compile q).embedding b) (List.mem_cons_self)
      exact ⟨(equation_dag_rename (compile q).embedding ρ ν hν a b).mp hab,
        (ih ρ).mpr ⟨ν,hν,fun e hm => he e (List.mem_cons_of_mem _ hm)⟩⟩
  | @gate Γ g q ih =>
    intro ρ
    constructor
    · rintro ⟨hg,hq⟩
      obtain ⟨ν,hν,hqν⟩ := (ih ρ).mp hq
      let gr := gateRename (compile q).embedding g
      let z := canonicalWitness (inputs ν) gr
      let μ := block ν 9 z
      refine ⟨μ,?_,?_⟩
      · intro x
        change block ν 9 z (shift 9 ((compile q).embedding x))=ρ x
        rw [block_shift]
        exact hν x
      · change ∀ e ∈ forest gr ++ (compile q).forest.map
          (fun e => (ScopedDAG.renameInput (shift 9) e.1,ScopedDAG.renameInput (shift 9) e.2)),
          SourceAdditionCompletion.Equation (inputs μ) e.1.term e.2.term
        intro e he
        rcases List.mem_append.mp he with he | he
        · have hl := (PrimitiveLowering.Proof.graphExact (compile q).context (inputs ν) gr z).mpr
            ⟨(gate_rename (compile q).embedding ρ ν hν g).mpr hg,rfl⟩
          rw [show inputs μ=PrimitiveLowering.extend (inputs ν) 9 z from inputs_block ν 9 z]
          exact hl e he
        · obtain ⟨e',he',heq⟩ := List.mem_map.mp he
          subst e
          exact (equation_dag_rename (shift 9) ν μ (block_shift ν 9 z) e'.1 e'.2).mpr (hqν e' he')
    · rintro ⟨ν,hν,hqν⟩
      let μ : Variable (compile q).context .ground → Nat := fun x => ν (shift 9 x)
      let z : Fin 9 → Nat := fun i => ν (fresh i)
      let gr := gateRename (compile q).embedding g
      have hd : block μ 9 z=ν := block_decompose 9 ν
      have hp : ∀ x, μ ((compile q).embedding x)=ρ x := hν
      have hl : ∀ e ∈ forest gr, SourceAdditionCompletion.Equation
          (PrimitiveLowering.extend (inputs μ) 9 z) e.1.term e.2.term := by
        rw [← inputs_block,hd]
        intro e he
        exact hqν e (List.mem_append_left _ he)
      have hg := ((PrimitiveLowering.Proof.graphExact (compile q).context (inputs μ) gr z).mp hl).1
      refine ⟨(gate_rename (compile q).embedding ρ μ hp g).mp hg,(ih ρ).mpr ⟨μ,hp,?_⟩⟩
      intro e he
      apply (equation_dag_rename (shift 9) μ ν (fun _ => rfl) e.1 e.2).mp
      apply hqν (ScopedDAG.renameInput (shift 9) e.1,ScopedDAG.renameInput (shift 9) e.2)
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨e,he,rfl⟩
  | @existsGround Γ q ih =>
    intro ρ
    constructor
    · rintro ⟨n,hn⟩
      obtain ⟨ν,hν,hq⟩ := (ih (extend ρ n)).mp hn
      exact ⟨ν,fun x => hν (.there x),hq⟩
    · rintro ⟨ν,hν,hq⟩
      refine ⟨ν ((compile q).embedding .here),(ih _).mpr ⟨ν,?_,hq⟩⟩
      intro x
      cases x with
      | here => rfl
      | there x => exact hν x
end LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
