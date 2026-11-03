module
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionTargets
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderExpansion.Proof

theorem kernel_ge (h c t : Nat) : t ≤ kernel h c t :=
  iterate_self_le (fun x => (self_lt_Phi x).le) _ t

theorem bottomInput_ge (n c t : Nat) : t ≤ bottomInput n c t := by
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih => exact (kernel_ge _ _ _).trans (ih _)

private theorem entries_nonempty (n c t : Nat) : entries n c t ≠ [] := by
  cases n <;> simp [entries]

private theorem entries_length (n c t : Nat) : (entries n c t).length = n+1 := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [entries, ih]

private theorem entries_ranks (n c t : Nat) :
    (entries n c t).map Prod.fst = (List.range (n+1)).reverse.map (fun i => i+3) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [entries, List.map_cons, ih, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.map_append,
      List.map_singleton, List.singleton_append]

private theorem entries_last (n c t : Nat) :
    (entries n c t).getLast? = some (3, bottomInput n c t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [entries, List.getLast?_cons_of_ne_nil (entries_nonempty _ _ _), ih]
    rfl

private theorem entry_domains (n c t : Nat) (ht : threshold n c ≤ t) :
    ∀ p ∈ entries n c t, 3 ≤ p.1 ∧ p.1 ≤ n+3 ∧
      t ≤ p.2 ∧ c+2*p.1+1 ≤ p.2 := by
  induction n generalizing t with
  | zero =>
    intro p hp
    have hp' : p = (3,t) := by simpa [entries] using hp
    subst p
    dsimp [threshold] at ht
    exact ⟨le_rfl,le_rfl,le_rfl,by omega⟩
  | succ n ih =>
    intro p hp
    rcases List.mem_cons.mp hp with he | hm
    · subst p
      dsimp [threshold] at ht
      exact ⟨by omega,by omega,le_rfl,by omega⟩
    · have hentry := kernel_ge (n+4) (c+n+4) t
      have htail : threshold n c ≤ kernel (n+4) (c+n+4) t := by
        dsimp [threshold] at *
        omega
      obtain ⟨h3,hr,hge,hd⟩ := ih _ htail p hm
      exact ⟨h3,by omega,hentry.trans hge,hd⟩

theorem exactEntryDomains : Targets.ExactEntryDomains := by
  intro n c t ht
  exact ⟨entries_ranks n c t, entries_last n c t, bottomInput_ge n c t,
    (bottomInput_ge n c t).trans (kernel_ge _ _ _), entry_domains n c t ht,
    by simp only [residuals, List.length_map, entries_length]⟩

end LogicLineages.OrdinalComparison.CounterLeaderExpansion.Proof
