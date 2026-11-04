module
public import LogicLineages.OrdinalComparison.ParametricPairWorklistChildrenProof
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Proof
open ParametricFinitePairCollapse

/-- Fuel concatenation preserves the actual task and value stacks. -/
theorem run_append (G : Nat → Nat) (n m : Nat) (s : State) :
    run G (n+m) s = run G m (run G n s) := by
  simp only [run, Nat.add_comm n m, Function.iterate_add_apply]

/-- Executing a list leaves its values in the stack's reverse order. -/
theorem execute_list (G : Nat → Nat) (qs : List (Nat × Nat))
    (h : ∀ q ∈ qs, ∀ (ts : List Task) (vs : List Nat),
      ∃ fuel, run G fuel (Sum.inl q::ts,vs) = (ts,value G q::vs))
    (ts : List Task) (vs : List Nat) :
    ∃ fuel, run G fuel (qs.map Sum.inl ++ ts,vs) =
      (ts,(qs.map (value G)).reverse ++ vs) := by
  induction qs generalizing ts vs with
  | nil => exact ⟨0,rfl⟩
  | cons q qs ih =>
    obtain ⟨n,hn⟩ := h q (by simp) (qs.map Sum.inl ++ ts) vs
    obtain ⟨m,hm⟩ := ih (fun r hr => h r (by simp [hr])) ts (value G q::vs)
    refine ⟨n+m,?_⟩
    rw [run_append]
    change run G m (run G n (Sum.inl q::(qs.map Sum.inl ++ ts),vs)) = _
    rw [hn,hm]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

/-- The combine instruction is precisely the maximum of the successors. -/
theorem combine_le_iff (vs : List Nat) (n : Nat) :
    combine vs ≤ n ↔ ∀ v ∈ vs, v+1 ≤ n := by
  induction vs with
  | nil => simp [combine]
  | cons v vs ih =>
    change max (v+1) (combine vs) ≤ n ↔ _
    simp only [max_le_iff,ih,List.mem_cons,forall_eq_or_imp]

theorem combine_children (G : Nat → Nat) (p : Nat × Nat) :
    combine ((children G p).map (value G)).reverse = value G p := by
  apply Nat.le_antisymm
  · rw [combine_le_iff]
    intro v hv
    simp only [List.mem_reverse,List.mem_map] at hv
    obtain ⟨q,hq,rfl⟩ := hv
    rw [ParametricFinitePairCollapse.Proof.exactMaximum G p]
    exact Finset.le_sup (f := fun q => value G q+1) ((children_mem G p q).mp hq)
  · rw [ParametricFinitePairCollapse.Proof.exactMaximum G p]
    apply Finset.sup_le
    intro q hq
    apply (combine_le_iff _ _).mp (Nat.le_refl _) (value G q)
    simp only [List.mem_reverse,List.mem_map]
    exact ⟨q,(children_mem G p q).mpr hq,rfl⟩

/-- A node's execution follows from the executions of its exact children. -/
theorem calibrate_of_children (G : Nat → Nat) (p : Nat × Nat)
    (h : ∀ q ∈ children G p, ∀ (ts : List Task) (vs : List Nat),
      ∃ fuel, run G fuel (Sum.inl q::ts,vs) = (ts,value G q::vs))
    (ts : List Task) (vs : List Nat) :
    ∃ fuel, run G fuel (Sum.inl p::ts,vs) = (ts,value G p::vs) := by
  let qs := children G p
  let ws := (qs.map (value G)).reverse
  have hw : ws.length = qs.length := by simp [ws]
  obtain ⟨n,hn⟩ := execute_list G qs h (Sum.inr qs.length::ts) vs
  have htake : (ws ++ vs).take qs.length = ws := by
    rw [← hw]
    exact List.take_left
  have hdrop : (ws ++ vs).drop qs.length = vs := by
    rw [← hw]
    exact List.drop_left
  have hk : qs.length ≤ (ws ++ vs).length := by simp [← hw]
  have hc : combine ws = value G p := combine_children G p
  refine ⟨1+n+1,?_⟩
  rw [run_append,run_append]
  have hfirst : run G 1 (Sum.inl p::ts,vs) =
      (qs.map Sum.inl ++ Sum.inr qs.length::ts,vs) := rfl
  rw [hfirst,hn]
  change step G (Sum.inr qs.length::ts,ws ++ vs) = _
  simp only [step,if_pos hk,htake,hdrop,hc]

/-- Lexicographic well-founded induction calibrates every continuation. -/
theorem continuationCalibration : Targets.ContinuationCalibration := by
  intro G p
  rcases p with ⟨a,b⟩
  induction a using Nat.strong_induction_on generalizing b with
  | h a iha =>
    induction b using Nat.strong_induction_on with
    | h b ihb =>
      apply calibrate_of_children G (a,b)
      intro q hq
      have hbelow := (ParametricFinitePairCollapse.Proof.predecessor_test G (a,b) q).mp
        ((children_mem G (a,b) q).mp hq)
      rcases q with ⟨c,d⟩
      rcases hbelow.1 with hlt | ⟨heq,hlt⟩
      · exact iha c hlt d
      · change c = a at heq
        subst c
        exact ihb d hlt
end LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Proof
