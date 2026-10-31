module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanTargets
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringStatementChecks
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGStatementChecks
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
open GroundEquivalence

theorem size : Targets.Size := by
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
      have hp := PrimitiveLowering.StatementChecks.fixedSize (compile q).context
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

theorem weight_identity {Γ} (es : List (Input Γ .ground × Input Γ .ground)) :
    ScopedDAG.weight es =
      2*(es.map (fun e => e.1.specs.length+e.2.specs.length)).sum+8*es.length+1 := by
  induction es with
  | nil => simp [ScopedDAG.weight]
  | cons e es ih =>
      simp only [ScopedDAG.weight,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

theorem result_weight {Γ} (r : Result Γ) :
    ScopedDAG.weight r.forest = 2*r.nodes+8*r.forest.length+1 := weight_identity r.forest

theorem pair_size_bounds (Γ : List Ty) (q : Plan Γ) :
    (strictPair q).1.specs.length ≤ 2*q.vertices+8*q.equations+1 ∧
    (strictPair q).2.specs.length ≤ 2*q.vertices+8*q.equations+1 ∧
    (weakPair q).1.specs.length ≤ 2*q.vertices+8*q.equations+7 ∧
    (weakPair q).2.specs.length ≤ 2*q.vertices+8*q.equations+7 := by
  have hs := size Γ q
  have ha := ScopedDAG.StatementChecks.aggregate (compile q).context (compile q).forest
  have hw : ScopedDAG.weight (compile q).forest ≤ 2*q.vertices+8*q.equations+1 := by
    rw [result_weight]
    omega
  have hleft : (strictPair q).1.specs.length ≤ 2*q.vertices+8*q.equations+1 := by
    change (ScopedDAG.aggregate (compile q).forest).2.specs.length ≤ _
    rw [ha.2.2]
    exact hw
  have hright : (strictPair q).2.specs.length ≤ 2*q.vertices+8*q.equations+1 := by
    change (ScopedDAG.aggregate (compile q).forest).1.specs.length ≤ _
    rw [ha.2.1]
    exact hw
  refine ⟨hleft,hright,?_,?_⟩
  · change (upperInput (strictPair q).1).specs.length ≤ _
    rw [GroundEquivalence.Proof.upper_size]
    omega
  · change (lowerInput (strictPair q).2).specs.length ≤ _
    rw [GroundEquivalence.Proof.lower_size]
    omega
end LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
