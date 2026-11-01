module
public import LogicLineages.OrdinalComparison.ComparisonAssemblyListProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonAssembly

attribute [local irreducible] encodedComparisonQueryNode encodedComparisonQueryLayers
  encodedComparisonQueryLayer encodedComparisonQueryTable encodedComparisonQueryResult
  encodedOneVariableSignDecision

theorem layer_program : Computable₂ encodedComparisonQueryLayer := by
  have hquery : Computable (fun p : (List ComparisonQuery × ComparisonNodeTable) × (ComparisonQuery × ComparisonNodeTable) => p.2.1) :=
    Computable.fst.comp Computable.snd
  have htable : Computable (fun p : (List ComparisonQuery × ComparisonNodeTable) × (ComparisonQuery × ComparisonNodeTable) => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hnode := node_program.comp hquery htable
  have hstep : Computable₂ (fun p : List ComparisonQuery × ComparisonNodeTable =>
      fun state : ComparisonQuery × ComparisonNodeTable =>
        (state.1,encodedComparisonQueryNode state.1 p.2)::state.2) :=
    Computable.list_cons.comp (hquery.pair hnode) (Computable.snd.comp Computable.snd)
  apply (computable_foldr ((0,0),(0,0)) Computable.fst Computable.snd hstep).of_eq
  intro p
  rcases p with ⟨nodes,table⟩
  unfold encodedComparisonQueryLayer
  change nodes.foldr (fun q acc => (q,encodedComparisonQueryNode q table)::acc) table=
    nodes.map (fun q => (q,encodedComparisonQueryNode q table))++table
  induction nodes with
  | nil => rfl
  | cons q rest ih => simpa only [List.foldr_cons,List.map_cons,List.cons_append] using congrArg (List.cons _) ih

theorem table_program : Computable encodedComparisonQueryTable := by
  have hs : Computable₂ (fun (_ : List (List ComparisonQuery)) => fun state : List ComparisonQuery × ComparisonNodeTable =>
      encodedComparisonQueryLayer state.1 state.2) :=
    layer_program.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
  apply (computable_foldr [] Computable.id (Computable.const []) hs).of_eq
  intro layers
  unfold encodedComparisonQueryTable
  rfl

theorem result_program : Computable encodedComparisonQueryResult := by
  have ht : Computable (fun q : ComparisonQuery => encodedComparisonQueryTable (encodedComparisonQueryLayers q)) :=
    table_program.comp ComparisonQuery.layers_program.1
  have hhead : Computable (fun q : ComparisonQuery => (encodedComparisonQueryTable (encodedComparisonQueryLayers q)).head?) :=
    Primrec.list_head?.to_comp.comp ht
  have hd : Computable (fun q : ComparisonQuery => (q,((1,1) : ComparisonNodeResult))) :=
    Computable.id.pair (Computable.const (1,1))
  apply (Computable.snd.comp (Computable.option_getD hhead hd)).of_eq
  intro q
  unfold encodedComparisonQueryResult
  cases encodedComparisonQueryTable (encodedComparisonQueryLayers q) <;> rfl

theorem decision_program : Computable₂ encodedOneVariableSignDecision := by
  apply (result_program.comp (Computable.id.pair (Computable.const (1,1)))).of_eq
  intro p
  unfold encodedOneVariableSignDecision
  rfl

theorem assembly_programs : Targets.ActualComparisonQueryAssemblyPrograms :=
  ⟨layer_program,table_program,result_program,decision_program⟩

end LogicLineages.OrdinalComparison.ComparisonAssembly
