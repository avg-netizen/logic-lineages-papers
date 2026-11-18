module
public import LogicLineages.PermittedControl.OriginalUnitOrderProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
 theorem initial_at_most_quadratic_units (delta : Ordinal.{0}) (hd : delta < epsilonZero)
    (hl : Order.IsSuccLimit delta) (hs : ∀ e ∈ initialPeelingUnits delta, e ≤ 2) :
    ∃ q n : Nat, originalGapUnits delta=Ordinal.log Ordinal.omega0 delta :: (List.replicate q (2 : Ordinal) ++ List.replicate n (1 : Ordinal)) ∧
      delta=Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)+
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
  exact ⟨q,n,by rw [hlst,hqn],by simpa only [add_assoc] using heval.symm⟩

end LogicLineages.PermittedControl
