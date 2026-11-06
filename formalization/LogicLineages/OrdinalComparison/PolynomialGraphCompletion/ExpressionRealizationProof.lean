module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof

public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionRealizationProof
open ExpressionSupportProof ExpressionNodeProof

theorem not_allocated_below (start : Nat) (t : Expr) (i : Nat)
    (hi : i < start) : i ∉ allocated start t := by
  intro hm
  have h := (mem_allocated start t i).mp hm
  omega

private theorem graph_names_below (start : Nat) (t : Expr) (stop : Nat)
    (hf : Fresh start t) (hs : start+nodeCount t ≤ stop) :
    ∀ i, i ∈ t.variables ∨ i ∈ allocated start t → i < stop := by
  intro i hi
  rcases hi with hsource | hnode
  · have h := hf i hsource
    omega
  · have h := (mem_allocated start t i).mp hnode
    omega

private theorem graph_frame_after (start : Nat) (t : Expr) (next : Nat) (u : Expr)
    (ν σ : Nat → Nat) (hf : Fresh start t) (hn : start+nodeCount t ≤ next)
    (hframe : ∀ i, i ∉ allocated next u → σ i = ν i) :
    GraphHolds start t σ ↔ GraphHolds start t ν :=
  graph_holds_congr start t σ ν (fun i hi =>
    hframe i (not_allocated_below next u i (graph_names_below start t next hf hn i hi)))

private theorem graph_update_after (start : Nat) (t : Expr) (ν : Nat → Nat)
    (k value : Nat) (hf : Fresh start t) (hk : start+nodeCount t ≤ k) :
    GraphHolds start t (Function.update ν k value) ↔ GraphHolds start t ν := by
  apply graph_holds_congr
  intro i hi
  have hne : i ≠ k := Nat.ne_of_lt (graph_names_below start t k hf hk i hi)
  exact Function.update_of_ne hne _ _

theorem source_frame (t u : Expr) (start : Nat) (ν σ : Nat → Nat)
    (hf : Fresh start t) (hframe : ∀ i, i ∉ allocated start u → σ i = ν i) :
    t.value σ = t.value ν :=
  source_value_congr t σ ν (fun i hi =>
    hframe i (not_allocated_below start u i (hf i hi)))

/-- This is only the finite-variable framing argument common to the two
literal unary constructors. F is their mathematical value function; no new
letter, observation, or equation is inserted into the word language. -/
private theorem realize_unary (hHead : Targets.HeadEquationExact)
    (start : Nat) (a t : Expr) (ha : ValidExpr a) (ν : Nat → Nat)
    (hf : Fresh start t) (hvars : t.variables = a.variables)
    (halloc : allocated start t = allocated start a ++ [output start t])
    (hout : output start t = start+nodeCount a) (F : Nat → Nat)
    (hvalue : t.value ν = F (a.value ν))
    (hgraph : ∀ σ : Nat → Nat, GraphHolds start t σ ↔
      GraphHolds start a σ ∧ σ (output start t) = F (σ (output start a)))
    (hchild : ∃ μ : Nat → Nat,
      (∀ i, i ∉ allocated start a → μ i = ν i) ∧
      GraphHolds start a μ ∧ μ (output start a) = a.value ν) :
    ∃ σ : Nat → Nat, (∀ i, i ∉ allocated start t → σ i = ν i) ∧
      GraphHolds start t σ ∧ σ (output start t) = t.value ν := by
  have hfa : Fresh start a := by
    intro i hi
    apply hf i
    rw [hvars]
    exact hi
  obtain ⟨μ,hframeA,hgraphA,_⟩ := hchild
  let z := output start t
  let σ := Function.update μ z (t.value ν)
  have hframe : ∀ i, i ∉ allocated start t → σ i = ν i := by
    intro i hi
    have hna : i ∉ allocated start a := by
      intro hm
      apply hi
      rw [halloc]
      exact List.mem_append_left _ hm
    have hne : i ≠ z := by
      intro he
      apply hi
      rw [halloc]
      exact List.mem_append_right _ (by
        simp only [List.mem_singleton]
        exact he)
    calc
      σ i = μ i := Function.update_of_ne hne _ _
      _ = ν i := hframeA i hna
  have hgraphAσ : GraphHolds start a σ :=
    (graph_update_after start a μ z _ hfa (by dsimp [z]; omega)).mpr hgraphA
  have hσz : σ (output start t) = t.value ν := Function.update_self _ _ _
  refine ⟨σ,hframe,(hgraph σ).mpr ⟨hgraphAσ,?_⟩,hσz⟩
  rw [hσz,graphSoundness hHead start a ha σ hgraphAσ,
    source_frame a t start ν σ hfa hframe]
  exact hvalue

theorem totalGraphRealization (hHead : Targets.HeadEquationExact) :
    ExpressionTargets.TotalGraphRealization := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ht ν hf
      refine ⟨Function.update ν start n,?_,?_,?_⟩
      · intro i hi
        have hne : i ≠ start := by
          intro h
          apply hi
          rw [h]
          exact (mem_allocated start (.numeral n) start).mpr (by simp [nodeCount])
        exact Function.update_of_ne hne _ _
      · apply (graph_numeral start n _).mpr
        simp only [Function.update_self]
      · simp only [output,nodeCount,Nat.add_sub_cancel,Function.update_self,Expr.value]
  | «variable» j =>
      intro ht ν hf
      have hj : j < start := hf j (by simp [Expr.variables])
      refine ⟨Function.update ν start (ν j),?_,?_,?_⟩
      · intro i hi
        have hne : i ≠ start := by
          intro h
          apply hi
          rw [h]
          exact (mem_allocated start (.variable j) start).mpr (by simp [nodeCount])
        exact Function.update_of_ne hne _ _
      · apply (graph_variable start j _).mpr
        simp only [Function.update_self,Function.update_of_ne (Nat.ne_of_lt hj)]
      · simp only [output,nodeCount,Nat.add_sub_cancel,Function.update_self,Expr.value]
  | add a b iha ihb =>
      intro ht ν hf
      have hvalid := valid_add ht
      have hfa : Fresh start a := fun i hi => hf i (List.mem_append_left _ hi)
      have hfb : Fresh start b := fun i hi => hf i (List.mem_append_right _ hi)
      have hfb' : Fresh (start+nodeCount a) b := fresh_mono (by omega) hfb
      obtain ⟨μ,hframeA,hgraphA,_⟩ := iha start hvalid.1 ν hfa
      obtain ⟨τ,hframeB,hgraphB,_⟩ := ihb (start+nodeCount a) hvalid.2 μ hfb'
      let z := start+nodeCount a+nodeCount b
      have hz : output start (.add a b) = z := by
        simp only [output,nodeCount]
        dsimp [z]
        omega
      let σ := Function.update τ z ((Expr.add a b).value ν)
      have hframe : ∀ i, i ∉ allocated start (.add a b) → σ i = ν i := by
        intro i hi
        have hna : i ∉ allocated start a := by
          intro ha
          apply hi
          rw [allocated_add]
          exact List.mem_append_left _ (List.mem_append_left _ ha)
        have hnb : i ∉ allocated (start+nodeCount a) b := by
          intro hb
          apply hi
          rw [allocated_add]
          exact List.mem_append_left _ (List.mem_append_right _ hb)
        have hne : i ≠ z := by
          intro he
          apply hi
          rw [allocated_add]
          exact List.mem_append_right _ (by
            simp only [List.mem_singleton]
            exact he.trans hz.symm)
        calc
          σ i = τ i := Function.update_of_ne hne _ _
          _ = μ i := hframeB i hnb
          _ = ν i := hframeA i hna
      have hgraphAτ := (graph_frame_after start a (start+nodeCount a) b μ τ hfa
        (by omega) hframeB).mpr hgraphA
      have hgraphAσ : GraphHolds start a σ :=
        (graph_update_after start a τ z _ hfa (by dsimp [z]; omega)).mpr hgraphAτ
      have hgraphBσ : GraphHolds (start+nodeCount a) b σ :=
        (graph_update_after (start+nodeCount a) b τ z _ hfb'
          (by dsimp [z]; omega)).mpr hgraphB
      have hσz : σ z = (Expr.add a b).value ν := Function.update_self _ _ _
      refine ⟨σ,hframe,(graph_add start a b σ).mpr ⟨hgraphAσ,hgraphBσ,?_⟩,?_⟩
      · rw [hz,hσz,graphSoundness hHead start a hvalid.1 σ hgraphAσ,
          graphSoundness hHead (start+nodeCount a) b hvalid.2 σ hgraphBσ,
          source_frame a (.add a b) start ν σ hfa hframe,
          source_frame b (.add a b) start ν σ hfb hframe]
        rfl
      · rw [hz]
        exact hσz
  | scale k a ih =>
      intro ht ν hf
      have ha := valid_scale ht
      apply realize_unary hHead start a (.scale k a) ha ν hf rfl
        (allocated_scale start k a) (by simp [output,nodeCount])
        (fun x => k*x) rfl (fun σ => graph_scale start k a σ)
      exact ih start ha ν hf
  | collapse code a ih =>
      intro ht ν hf
      have hvalid := valid_collapse ht
      apply realize_unary hHead start a (.collapse code a) hvalid.1 ν hf rfl
        (allocated_collapse start code a) (by simp [output,nodeCount])
        (headValue code) rfl (fun σ => graph_collapse hHead start code a hvalid.2 σ)
      exact ih start hvalid.1 ν hf

theorem allocatedNodeUniqueness (hHead : Targets.HeadEquationExact) :
    ExpressionTargets.AllocatedNodeUniqueness := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ht ν σ hsource hν hσ i hi
      have hi' := (mem_allocated start (.numeral n) i).mp hi
      have he : i = start := by simp only [nodeCount] at hi'; omega
      rw [he,(graph_numeral start n ν).mp hν,(graph_numeral start n σ).mp hσ]
  | «variable» j =>
      intro ht ν σ hsource hν hσ i hi
      have hi' := (mem_allocated start (.variable j) i).mp hi
      have he : i = start := by simp only [nodeCount] at hi'; omega
      rw [he,(graph_variable start j ν).mp hν,(graph_variable start j σ).mp hσ]
      exact hsource j (by simp [Expr.variables])
  | add a b iha ihb =>
      intro ht ν σ hsource hν hσ i hi
      have hvalid := valid_add ht
      have hsourceA : ∀ j ∈ a.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_left _ hj)
      have hsourceB : ∀ j ∈ b.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_right _ hj)
      obtain ⟨haν,hbν,_⟩ := (graph_add start a b ν).mp hν
      obtain ⟨haσ,hbσ,_⟩ := (graph_add start a b σ).mp hσ
      rw [allocated_add] at hi
      simp only [List.mem_append,List.mem_singleton] at hi
      rcases hi with (hi | hi) | hi
      · exact iha start hvalid.1 ν σ hsourceA haν haσ i hi
      · exact ihb (start+nodeCount a) hvalid.2 ν σ hsourceB hbν hbσ i hi
      · rw [hi,graphSoundness hHead start (.add a b) ht ν hν,
          graphSoundness hHead start (.add a b) ht σ hσ]
        exact source_value_congr (.add a b) ν σ hsource
  | scale k a ih =>
      intro ht ν σ hsource hν hσ i hi
      have ha := valid_scale ht
      obtain ⟨haν,_⟩ := (graph_scale start k a ν).mp hν
      obtain ⟨haσ,_⟩ := (graph_scale start k a σ).mp hσ
      rw [allocated_scale] at hi
      simp only [List.mem_append,List.mem_singleton] at hi
      rcases hi with hi | hi
      · exact ih start ha ν σ hsource haν haσ i hi
      · rw [hi,graphSoundness hHead start (.scale k a) ht ν hν,
          graphSoundness hHead start (.scale k a) ht σ hσ]
        exact source_value_congr (.scale k a) ν σ hsource
  | collapse code a ih =>
      intro ht ν σ hsource hν hσ i hi
      have hvalid := valid_collapse ht
      obtain ⟨haν,_⟩ := (graph_collapse hHead start code a hvalid.2 ν).mp hν
      obtain ⟨haσ,_⟩ := (graph_collapse hHead start code a hvalid.2 σ).mp hσ
      rw [allocated_collapse] at hi
      simp only [List.mem_append,List.mem_singleton] at hi
      rcases hi with hi | hi
      · exact ih start hvalid.1 ν σ hsource haν haσ i hi
      · rw [hi,graphSoundness hHead start (.collapse code a) ht ν hν,
          graphSoundness hHead start (.collapse code a) ht σ hσ]
        exact source_value_congr (.collapse code a) ν σ hsource

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionRealizationProof
