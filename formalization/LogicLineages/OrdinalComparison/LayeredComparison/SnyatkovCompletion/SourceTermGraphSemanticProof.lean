module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSemanticProof
open CommonLayerSyntax NormalForm SourceTermGraph SourceTermGraphSupportProof

private theorem negated_sum (xs : List (Int × Summand)) (ν : Nat → Nat) :
    ((xs.map (fun a => (-a.1, a.2))).map
      (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      -((xs.map (fun a => a.1 * (a.2.term.value ν : Int))).sum) := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, neg_zero]
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, neg_mul, ih]
      omega

theorem negateRow_value (row : Row) (ν : Nat → Nat) :
    rowValue (SourceTermGraph.negateRow row) ν = -rowValue row ν := by
  simp only [SourceTermGraph.negateRow, rowValue, negated_sum]
  omega

theorem equation_eval (row : Row) (ν : Nat → Nat) :
    (equation row).eval ν ↔ rowValue row ν = 0 := by
  simp only [equation, NormalForm.Formula.eval, NormalForm.Atom.eval, negateRow_value]
  omega

theorem equations_eval (rs : List Row) (ν : Nat → Nat) :
    (equations rs).eval ν ↔ ∀ row ∈ rs, rowValue row ν = 0 := by
  induction rs with
  | nil => simp only [equations, List.foldr_nil, NormalForm.Formula.eval,
      List.not_mem_nil, false_implies, implies_true]
  | cons row rest ih =>
      change ((equation row).eval ν ∧ (equations rest).eval ν) ↔ _
      simp only [equation_eval, ih, List.mem_cons, forall_eq_or_imp]

theorem equations_append (rs ss : List Row) (ν : Nat → Nat) :
    (equations (rs ++ ss)).eval ν ↔ (equations rs).eval ν ∧ (equations ss).eval ν := by
  simp only [equations_eval, List.mem_append, or_imp, forall_and]

theorem equations_singleton (row : Row) (ν : Nat → Nat) :
    (equations [row]).eval ν ↔ (equation row).eval ν := by
  simp only [equations, List.foldr_cons, List.foldr_nil, NormalForm.Formula.eval, and_true]

theorem numeral_equation (z n : Nat) (ν : Nat → Nat) :
    (equation (numeralRow z n)).eval ν ↔ ν z = n := by
  rw [equation_eval]
  simp only [numeralRow, rowValue, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Summand.term, Term.value, one_mul, add_zero]
  omega

theorem variable_equation (z i : Nat) (ν : Nat → Nat) :
    (equation (variableRow z i)).eval ν ↔ ν z = ν i := by
  rw [equation_eval]
  simp only [variableRow, rowValue, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Summand.term, Term.value, one_mul, neg_one_mul, add_zero, zero_add]
  omega

theorem addition_equation (z x y : Nat) (ν : Nat → Nat) :
    (equation (additionRow z x y)).eval ν ↔ ν z = ν x + ν y := by
  rw [equation_eval]
  simp only [additionRow, rowValue, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Summand.term, Term.value, one_mul, neg_one_mul, add_zero, zero_add]
  omega

theorem phi_equation (z x : Nat) (ν : Nat → Nat) :
    (equation (phiRow z x)).eval ν ↔ ν z = Phi (ν x) := by
  rw [equation_eval]
  simp only [phiRow, rowValue, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Summand.term, shiftTerm, Term.value, Int.toNat_zero, neg_zero,
    Nat.sub_zero, one_mul, neg_one_mul, add_zero, zero_add]
  omega

theorem graph_numeral (start n : Nat) (ν : Nat → Nat) :
    (graph start (.numeral n)).eval ν ↔ ν start = n := by
  simp only [graph, rows, equations_singleton, numeral_equation]

theorem graph_variable (start i : Nat) (ν : Nat → Nat) :
    (graph start (.variable i)).eval ν ↔ ν start = ν i := by
  simp only [graph, rows, equations_singleton, variable_equation]

theorem graph_add (start : Nat) (a b : BaseTerm) (ν : Nat → Nat) :
    (graph start (.add a b)).eval ν ↔
      (graph start a).eval ν ∧ (graph (start + nodeCount a) b).eval ν ∧
      ν (output start (.add a b)) = ν (output start a) + ν (output (start + nodeCount a) b) := by
  simp only [graph, rows, equations_append, equations_singleton, addition_equation, and_assoc]

theorem graph_phi (start : Nat) (a : BaseTerm) (ν : Nat → Nat) :
    (graph start (.phi a)).eval ν ↔
      (graph start a).eval ν ∧ ν (output start (.phi a)) = Phi (ν (output start a)) := by
  simp only [graph, rows, equations_append, equations_singleton, phi_equation]

theorem graphSoundness : SourceTermGraphTargets.GraphSoundness := by
  intro start t ν
  induction t generalizing start with
  | numeral n =>
      intro h
      simpa only [output, nodeCount, Nat.add_sub_cancel, BaseTerm.value] using
        (graph_numeral start n ν).mp h
  | «variable» i =>
      intro h
      simpa only [output, nodeCount, Nat.add_sub_cancel, BaseTerm.value] using
        (graph_variable start i ν).mp h
  | add a b iha ihb =>
      intro h
      obtain ⟨ha, hb, hout⟩ := (graph_add start a b ν).mp h
      rw [iha start ha, ihb (start + nodeCount a) hb] at hout
      exact hout
  | phi a ih =>
      intro h
      obtain ⟨ha, hout⟩ := (graph_phi start a ν).mp h
      rw [ih start ha] at hout
      exact hout

private theorem not_allocated_below (start : Nat) (t : BaseTerm) (i : Nat)
    (hi : i < start) : i ∉ allocated start t := by
  intro hm
  have h := (mem_allocated start t i).mp hm
  omega

private theorem graph_names_below (start : Nat) (t : BaseTerm) (stop : Nat)
    (hf : Fresh start t) (hs : start + nodeCount t ≤ stop) :
    ∀ i, i ∈ t.variables ∨ i ∈ allocated start t → i < stop := by
  intro i hi
  rcases hi with hsource | hnode
  · have h := hf i hsource
    omega
  · have h := (mem_allocated start t i).mp hnode
    omega

private theorem graph_frame_after (start : Nat) (t : BaseTerm) (next : Nat) (u : BaseTerm)
    (ν σ : Nat → Nat) (hf : Fresh start t) (hn : start + nodeCount t ≤ next)
    (hframe : ∀ i, i ∉ allocated next u → σ i = ν i) :
    (graph start t).eval σ ↔ (graph start t).eval ν :=
  graph_eval_congr start t σ ν (fun i hi =>
    hframe i (not_allocated_below next u i (graph_names_below start t next hf hn i hi)))

private theorem graph_update_after (start : Nat) (t : BaseTerm) (ν : Nat → Nat)
    (k value : Nat) (hf : Fresh start t) (hk : start + nodeCount t ≤ k) :
    (graph start t).eval (Function.update ν k value) ↔ (graph start t).eval ν := by
  apply graph_eval_congr
  intro i hi
  have hne : i ≠ k := Nat.ne_of_lt (graph_names_below start t k hf hk i hi)
  exact Function.update_of_ne hne _ _

private theorem source_frame (t u : BaseTerm) (start : Nat) (ν σ : Nat → Nat)
    (hf : Fresh start t) (hframe : ∀ i, i ∉ allocated start u → σ i = ν i) :
    t.value σ = t.value ν :=
  source_value_congr t σ ν (fun i hi =>
    hframe i (not_allocated_below start u i (hf i hi)))

theorem totalGraphRealization : SourceTermGraphTargets.TotalGraphRealization := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ν hf
      refine ⟨Function.update ν start n, ?_, ?_, ?_⟩
      · intro i hi
        have hne : i ≠ start := by
          intro h
          subst i
          exact hi ((mem_allocated start (.numeral n) start).mpr (by simp [nodeCount]))
        exact Function.update_of_ne hne _ _
      · apply (graph_numeral start n _).mpr
        simp only [Function.update_self]
      · simp only [output, nodeCount, Nat.add_sub_cancel, Function.update_self, BaseTerm.value]
  | «variable» j =>
      intro ν hf
      have hj : j < start := hf j (by simp only [BaseTerm.variables, List.mem_singleton])
      refine ⟨Function.update ν start (ν j), ?_, ?_, ?_⟩
      · intro i hi
        have hne : i ≠ start := by
          intro h
          subst i
          exact hi ((mem_allocated start (.variable j) start).mpr (by simp [nodeCount]))
        exact Function.update_of_ne hne _ _
      · apply (graph_variable start j _).mpr
        simp only [Function.update_self, Function.update_of_ne (Nat.ne_of_lt hj)]
      · simp only [output, nodeCount, Nat.add_sub_cancel, Function.update_self, BaseTerm.value]
  | add a b iha ihb =>
      intro ν hf
      have hfa : Fresh start a := fun i hi => hf i (List.mem_append_left _ hi)
      have hfb : Fresh start b := fun i hi => hf i (List.mem_append_right _ hi)
      have hfb' : Fresh (start + nodeCount a) b := fresh_mono (by omega) hfb
      obtain ⟨μ, hframeA, hgraphA, _⟩ := iha start ν hfa
      obtain ⟨τ, hframeB, hgraphB, _⟩ := ihb (start + nodeCount a) μ hfb'
      let z := start + nodeCount a + nodeCount b
      have hz : output start (.add a b) = z := by
        simp only [output, nodeCount]
        dsimp [z]
        omega
      let σ := Function.update τ z ((BaseTerm.add a b).value ν)
      have hframe : ∀ i, i ∉ allocated start (.add a b) → σ i = ν i := by
        intro i hi
        have hna : i ∉ allocated start a := by
          intro ha
          apply hi
          rw [allocated_add]
          simp only [List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inl ha)
        have hnb : i ∉ allocated (start + nodeCount a) b := by
          intro hb
          apply hi
          rw [allocated_add]
          simp only [List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inr hb)
        have hne : i ≠ z := by
          intro he
          apply hi
          rw [allocated_add]
          simp only [List.mem_append, List.mem_singleton]
          exact Or.inr (he.trans hz.symm)
        calc
          σ i = τ i := Function.update_of_ne hne _ _
          _ = μ i := hframeB i hnb
          _ = ν i := hframeA i hna
      have hgraphAτ := (graph_frame_after start a (start + nodeCount a) b μ τ hfa
        (by omega) hframeB).mpr hgraphA
      have hgraphAσ : (graph start a).eval σ :=
        (graph_update_after start a τ z _ hfa (by dsimp [z]; omega)).mpr hgraphAτ
      have hgraphBσ : (graph (start + nodeCount a) b).eval σ :=
        (graph_update_after (start + nodeCount a) b τ z _ hfb'
          (by dsimp [z]; omega)).mpr hgraphB
      have hσz : σ z = (BaseTerm.add a b).value ν := Function.update_self _ _ _
      refine ⟨σ, hframe, (graph_add start a b σ).mpr ⟨hgraphAσ, hgraphBσ, ?_⟩, ?_⟩
      · rw [hz, hσz, graphSoundness start a σ hgraphAσ,
          graphSoundness (start + nodeCount a) b σ hgraphBσ,
          source_frame a (.add a b) start ν σ hfa hframe,
          source_frame b (.add a b) start ν σ hfb hframe]
        rfl
      · rw [hz]
        exact hσz
  | phi a ih =>
      intro ν hf
      have hfa : Fresh start a := hf
      obtain ⟨μ, hframeA, hgraphA, _⟩ := ih start ν hfa
      let z := start + nodeCount a
      have hz : output start (.phi a) = z := by
        simp only [output, nodeCount]
        dsimp [z]
      let σ := Function.update μ z ((BaseTerm.phi a).value ν)
      have hframe : ∀ i, i ∉ allocated start (.phi a) → σ i = ν i := by
        intro i hi
        have hna : i ∉ allocated start a := by
          intro ha
          apply hi
          rw [allocated_phi]
          exact List.mem_append_left _ ha
        have hne : i ≠ z := by
          intro he
          apply hi
          rw [allocated_phi]
          exact List.mem_append_right _ (by
            simp only [List.mem_singleton]
            exact he.trans hz.symm)
        calc
          σ i = μ i := Function.update_of_ne hne _ _
          _ = ν i := hframeA i hna
      have hgraphAσ : (graph start a).eval σ :=
        (graph_update_after start a μ z _ hfa (by dsimp [z]; exact le_rfl)).mpr hgraphA
      have hσz : σ z = (BaseTerm.phi a).value ν := Function.update_self _ _ _
      refine ⟨σ, hframe, (graph_phi start a σ).mpr ⟨hgraphAσ, ?_⟩, ?_⟩
      · rw [hz, hσz, graphSoundness start a σ hgraphAσ,
          source_frame a (.phi a) start ν σ hfa hframe]
        rfl
      · rw [hz]
        exact hσz

theorem allocatedNodeUniqueness : SourceTermGraphTargets.AllocatedNodeUniqueness := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ν σ hsource hν hσ i hi
      have hi' := (mem_allocated start (.numeral n) i).mp hi
      have he : i = start := by simp only [nodeCount] at hi'; omega
      rw [he, (graph_numeral start n ν).mp hν, (graph_numeral start n σ).mp hσ]
  | «variable» j =>
      intro ν σ hsource hν hσ i hi
      have hi' := (mem_allocated start (.variable j) i).mp hi
      have he : i = start := by simp only [nodeCount] at hi'; omega
      rw [he, (graph_variable start j ν).mp hν, (graph_variable start j σ).mp hσ]
      exact hsource j (by simp only [BaseTerm.variables, List.mem_singleton])
  | add a b iha ihb =>
      intro ν σ hsource hν hσ i hi
      have hsourceA : ∀ j ∈ a.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_left _ hj)
      have hsourceB : ∀ j ∈ b.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_right _ hj)
      obtain ⟨haν, hbν, _⟩ := (graph_add start a b ν).mp hν
      obtain ⟨haσ, hbσ, _⟩ := (graph_add start a b σ).mp hσ
      rw [allocated_add] at hi
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with (hi | hi) | hi
      · exact iha start ν σ hsourceA haν haσ i hi
      · exact ihb (start + nodeCount a) ν σ hsourceB hbν hbσ i hi
      · rw [hi, graphSoundness start (.add a b) ν hν,
          graphSoundness start (.add a b) σ hσ]
        exact source_value_congr (.add a b) ν σ hsource
  | phi a ih =>
      intro ν σ hsource hν hσ i hi
      obtain ⟨haν, _⟩ := (graph_phi start a ν).mp hν
      obtain ⟨haσ, _⟩ := (graph_phi start a σ).mp hσ
      rw [allocated_phi] at hi
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | hi
      · exact ih start ν σ hsource haν haσ i hi
      · rw [hi, graphSoundness start (.phi a) ν hν,
          graphSoundness start (.phi a) σ hσ]
        exact source_value_congr (.phi a) ν σ hsource

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSemanticProof
