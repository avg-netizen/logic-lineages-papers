module
public import LogicLineages.PermittedControl.OriginalUnitsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem original_unit_cnf (delta e : Ordinal.{0}) (he : e ∈ originalGapUnits delta) :
    e ∈ (Ordinal.CNF Ordinal.omega0 delta).map Prod.fst := by
  obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp he
  exact List.mem_map.mpr ⟨p,hp,(List.mem_replicate.mp he).2.symm⟩

private theorem original_units_raw_order (a : ONote) (ha : ONote.NF a) :
    (originalGapUnits a.repr).Pairwise (fun e d => d ≤ e) := by
  induction a with
  | zero => simp [originalGapUnits,ONote.repr]
  | oadd e c t ihe iht =>
    rw [original_units_oadd e t c ha,List.pairwise_append]
    refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl),iht ha.snd,?_⟩
    intro x hx y hy
    have hx' := (List.mem_replicate.mp hx).2
    subst x
    have hmem := original_unit_cnf t.repr y hy
    obtain ⟨p,hp,hpy⟩ := List.mem_map.mp hmem
    have htne : t.repr ≠ 0 := by
      intro hz
      simpa only [hz,Ordinal.CNF.zero_right,List.not_mem_nil] using hp
    have hl : Ordinal.log Ordinal.omega0 t.repr < e.repr :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 htne).mp ha.snd'.repr_lt
    rw [← hpy]
    exact (Ordinal.CNF.fst_le_log hp).trans hl.le

 theorem original_units_order (delta : Ordinal.{0}) (hd : delta < epsilonZero) :
    (originalGapUnits delta).Pairwise (fun e d => d ≤ e) := by
  obtain ⟨a,rfl⟩ := normalRepresentationComplete delta hd
  exact original_units_raw_order a.1 a.2

 theorem binary_unit_list (l : List Ordinal.{0}) (horder : l.Pairwise (fun e d => d ≤ e))
    (hb : ∀ e ∈ l, 1 ≤ e ∧ e ≤ 2) :
    ∃ q n : Nat, l=List.replicate q (2 : Ordinal) ++ List.replicate n (1 : Ordinal) := by
  induction l with
  | nil => exact ⟨0,0,rfl⟩
  | cons e l ih =>
    have he := hb e List.mem_cons_self
    have hord := List.pairwise_cons.mp horder
    by_cases h2 : e=2
    · subst e
      obtain ⟨q,n,hn⟩ := ih hord.2 (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      refine ⟨q+1,n,?_⟩
      rw [List.replicate_succ,List.cons_append,← hn]
    · have hlt : e < (1 : Ordinal)+1 := by simpa using (lt_of_le_of_ne he.2 h2)
      have he1 : e=1 := le_antisymm (Order.lt_add_one_iff.mp hlt) he.1
      have hall : ∀ x ∈ e::l, x=(1 : Ordinal) := by
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · exact hx.trans he1
        · exact le_antisymm (by simpa only [he1] using hord.1 x hx) (hb x (List.mem_cons_of_mem _ hx)).1
      exact ⟨0,(e::l).length,by simpa using (List.eq_replicate_length.mpr hall)⟩

 theorem initial_at_most_quadratic_shape (delta : Ordinal.{0}) (hd : delta < epsilonZero)
    (hl : Order.IsSuccLimit delta) (hs : ∀ e ∈ initialPeelingUnits delta, e ≤ 2) :
    ∃ q n : Nat, delta=Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)+
      Ordinal.omega0^(2 : Ordinal)*(q : Ordinal)+Ordinal.omega0*(n : Ordinal) := by
  obtain ⟨l,hlst⟩ := original_units_head delta hd hl.bot_lt.ne'
  have hord := original_units_order delta hd
  rw [hlst,List.pairwise_cons] at hord
  obtain ⟨q,n,hqn⟩ := binary_unit_list l hord.2 (by
    intro e he
    exact ⟨original_units_positive delta hd hl e (by rw [hlst]; exact List.mem_cons_of_mem _ he),
      hs e (by simpa only [initialPeelingUnits,hlst,List.tail_cons,List.mem_reverse] using he)⟩)
  have heval := original_units_eval delta hd
  rw [hlst,List.map_cons,List.sum_cons,hqn,List.map_append,List.sum_append,
    List.map_replicate,List.map_replicate,List.sum_replicate,List.sum_replicate,
    Ordinal.opow_one,Ordinal.nsmul_eq_mul,Ordinal.nsmul_eq_mul] at heval
  exact ⟨q,n,by simpa only [add_assoc] using heval.symm⟩

end LogicLineages.PermittedControl
