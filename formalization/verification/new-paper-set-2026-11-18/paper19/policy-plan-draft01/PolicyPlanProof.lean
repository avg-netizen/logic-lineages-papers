module
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanSemanticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyPlan
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan GroundEquivalence PrimitiveLowering
theorem compilation : PolicyPlanTargets.Compilation := by
  intro f hf p Γ q
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
    simp only [Eval,compile,ResultHolds]
    constructor
    · rintro ⟨hab,hq⟩
      obtain ⟨ν,hν,he⟩ := (ih ρ).mp hq
      refine ⟨ν,hν,?_⟩
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (equation_dag_rename p f (compile q).embedding ρ ν hν a b).mpr hab
      · exact he e hm
    · rintro ⟨ν,hν,he⟩
      have hab := he (ScopedDAG.renameInput (compile q).embedding a,
        ScopedDAG.renameInput (compile q).embedding b) (List.mem_cons_self)
      exact ⟨(equation_dag_rename p f (compile q).embedding ρ ν hν a b).mp hab,
        (ih ρ).mpr ⟨ν,hν,fun e hm => he e (List.mem_cons_of_mem _ hm)⟩⟩
  | @gate Γ g q ih =>
    intro ρ
    constructor
    · rintro ⟨hg,hq⟩
      obtain ⟨ν,hν,hqν⟩ := (ih ρ).mp hq
      let gr := gateRename (compile q).embedding g
      let z := PolicyLowering.canonicalWitness f (inputs ν) gr
      let μ := block ν 9 z
      refine ⟨μ,?_,?_⟩
      · intro x
        change block ν 9 z (shift 9 ((compile q).embedding x))=ρ x
        rw [block_shift]
        exact hν x
      · change ∀ e ∈ forest gr ++ (compile q).forest.map
          (fun e => (ScopedDAG.renameInput (shift 9) e.1,ScopedDAG.renameInput (shift 9) e.2)),
          PolicyAddition.Equation p f (inputs μ) e.1.term e.2.term
        intro e he
        rcases List.mem_append.mp he with he | he
        · have hl := ((PolicyLowering.allGateExact f hf p (compile q).context (inputs ν) gr z).2).mpr
            ⟨(gate_rename (compile q).embedding ρ ν hν g).mpr hg,rfl⟩
          rw [show inputs μ=PrimitiveLowering.extend (inputs ν) 9 z from inputs_block ν 9 z]
          exact hl e he
        · obtain ⟨e',he',heq⟩ := List.mem_map.mp he
          subst e
          exact (equation_dag_rename p f (shift 9) ν μ (block_shift ν 9 z) e'.1 e'.2).mpr (hqν e' he')
    · rintro ⟨ν,hν,hqν⟩
      let μ : Variable (compile q).context .ground → Nat := fun x => ν (shift 9 x)
      let z : Fin 9 → Nat := fun i => ν (fresh i)
      let gr := gateRename (compile q).embedding g
      have hd : block μ 9 z=ν := block_decompose 9 ν
      have hp : ∀ x, μ ((compile q).embedding x)=ρ x := hν
      have hl : ∀ e ∈ forest gr, PolicyAddition.Equation p f
          (PrimitiveLowering.extend (inputs μ) 9 z) e.1.term e.2.term := by
        rw [← inputs_block,hd]
        intro e he
        exact hqν e (List.mem_append_left _ he)
      have hg := (((PolicyLowering.allGateExact f hf p (compile q).context (inputs μ) gr z).2).mp hl).1
      refine ⟨(gate_rename (compile q).embedding ρ μ hp g).mp hg,(ih ρ).mpr ⟨μ,hp,?_⟩⟩
      intro e he
      apply (equation_dag_rename p f (shift 9) μ ν (fun _ => rfl) e.1 e.2).mp
      apply hqν (ScopedDAG.renameInput (shift 9) e.1,ScopedDAG.renameInput (shift 9) e.2)
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨e,he,rfl⟩
  | @existsGround Γ q ih =>
    intro ρ
    constructor
    · rintro ⟨n,hn⟩
      obtain ⟨ν,hν,hq⟩ := (ih (ExistentialPlan.extend ρ n)).mp hn
      exact ⟨ν,fun x => hν (.there x),hq⟩
    · rintro ⟨ν,hν,hq⟩
      refine ⟨ν ((compile q).embedding .here),(ih _).mpr ⟨ν,?_,hq⟩⟩
      intro x
      cases x with
      | here => rfl
      | there x => exact hν x

theorem actualSize : PolicyPlanTargets.ActualSize := by
  intro Γ q
  induction q with
  | done => simp [compile,Result.nodes,Plan.vertices,Plan.equations,Plan.witnesses]
  | @equation Γ a b q ih =>
      rcases ih with ⟨hn,he,hc,hg⟩
      refine ⟨?_,?_,hc,hg⟩
      · change a.specs.length+b.specs.length+(compile q).nodes ≤ a.specs.length+b.specs.length+q.vertices
        omega
      · change (compile q).forest.length+1=1+q.equations
        omega
  | @gate Γ g q ih =>
      rcases ih with ⟨hn,he,hc,hg⟩
      have hp := PolicyLowering.actualFixedSize (compile q).context
        (gateRename (compile q).embedding g)
      refine ⟨?_,?_,?_,?_⟩
      · simp only [compile,Result.nodes,List.map_append,List.sum_append,List.map_map,
          Function.comp_def,ScopedDAG.renameInput]
        change PrimitiveLowering.forestNodes (gateRename (compile q).embedding g) +
          (compile q).nodes ≤ 80+q.vertices
        omega
      · simp only [compile,List.length_append,List.length_map]
        change (PrimitiveLowering.forest (gateRename (compile q).embedding g)).length +
          (compile q).forest.length = 10+q.equations
        omega
      · simp only [compile,PrimitiveLowering.Block,List.length_append,List.length_replicate]
        change 9+(compile q).context.length=Γ.length+(9+q.witnesses)
        omega
      · intro hΓ σ hσ
        change σ ∈ List.replicate 9 Ty.ground ++ (compile q).context at hσ
        rcases List.mem_append.mp hσ with hσ|hσ
        · simpa using hσ
        · exact hg hΓ σ hσ
  | @existsGround Γ q ih =>
      rcases ih with ⟨hn,he,hc,hg⟩
      refine ⟨hn,he,?_,?_⟩
      · change (compile q).context.length=Γ.length+(1+q.witnesses)
        simp only [List.length_cons] at hc
        omega
      · intro hΓ
        apply hg
        intro σ hσ
        rcases List.mem_cons.mp hσ with hσ|hσ
        · exact hσ
        · exact hΓ σ hσ


#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyPlan
end LogicLineages.ControlSensitivityCurrent.PolicyPlan
