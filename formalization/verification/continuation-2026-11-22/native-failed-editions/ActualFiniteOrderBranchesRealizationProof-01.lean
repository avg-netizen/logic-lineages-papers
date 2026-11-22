module
public import LogicLineages.PermittedControl.ActualFiniteOrderBranchesTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesGuardProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteOrderBranches

private theorem lookFind (key value : Entry → Nat) (j : Nat) (es : List Entry)
    (someEntry : ∃ e ∈ es, key e = j) :
    ∃ e ∈ es, key e = j ∧ look key value j es = value e := by
  induction es with
  | nil =>
      obtain ⟨e,member,_⟩ := someEntry
      cases member
  | cons top es ih =>
      by_cases eq : key top = j
      · exact ⟨top,List.mem_cons_self,eq,by rw [look,if_pos eq]⟩
      · obtain ⟨e,member,he⟩ := someEntry
        rcases List.mem_cons.mp member with ht | ht
        · subst e
          exact (eq he).elim
        · obtain ⟨x,hx,hk,hr⟩ := ih ⟨e,ht,he⟩
          exact ⟨x,List.mem_cons_of_mem _ hx,hk,by simpa only [look,if_neg eq] using hr⟩

private theorem leMaximum (θ : Nat → Nat) (es : List Entry) (e : Entry) (member : e ∈ es) :
    θ e.1 ≤ es.foldr (fun d b => max (θ d.1) b) 0 := by
  induction es with
  | nil => cases member
  | cons top es ih =>
      rcases List.mem_cons.mp member with h | h
      · subst e
        exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

private theorem pairLabel (θ : Nat → Nat) (p : Pattern) (comp : Compares θ p)
    (a b : Entry) (ha : a ∈ p.2) (hb : b ∈ p.2) (same : a.1 = b.1) : a.2 = b.2 := by
  rcases lt_trichotomy a.2 b.2 with lt | eq | gt
  · have impossible := (comp a ha b hb).2 lt
    rw [same] at impossible
    exact (Nat.lt_irrefl _ impossible).elim
  · exact eq
  · have impossible := (comp b hb a ha).2 gt
    rw [same] at impossible
    exact (Nat.lt_irrefl _ impossible).elim

theorem exactBranchRealization : ExactBranchRealization := by
  intro θ names p member ok
  obtain ⟨_,keys,bounds,all⟩ := (exactPatternEnumeration names p).mp member
  have comp := (exactOrderGuard θ p).mp ok
  have lookup (e : Entry) (he : e ∈ p.2) : rename p e.1 = e.2 := by
    obtain ⟨a,ha,key,value⟩ := lookFind Prod.fst Prod.snd e.1 p.2 ⟨e,he,rfl⟩
    exact value.trans (pairLabel θ p comp a e ha he key)
  have atRank (e : Entry) (he : e ∈ p.2) : realized θ p e.2 = θ e.1 := by
    obtain ⟨a,ha,key,value⟩ :=
      lookFind Prod.snd (fun x => θ x.1) e.2 p.2 ⟨e,he,rfl⟩
    rw [realized,if_pos (bounds e he)]
    exact value.trans ((comp a ha e he).1 key)
  refine ⟨?_,fun e he => ⟨lookup e he,atRank e he⟩,?_⟩
  · intro i j ordered
    by_cases hj : j < p.1
    · have hi := ordered.trans hj
      obtain ⟨a,ha,ea⟩ := all i hi
      obtain ⟨b,hb,eb⟩ := all j hj
      rw [← ea,← eb,atRank a ha,atRank b hb]
      exact (comp a ha b hb).2 (by rw [ea,eb]; exact ordered)
    · by_cases hi : i < p.1
      · obtain ⟨a,ha,ea⟩ := all i hi
        have left : realized θ p i = θ a.1 := by rw [← ea,atRank a ha]
        rw [left,realized θ p j,if_neg hj]
        have bound := leMaximum θ p.2 a ha
        omega
      · rw [realized θ p i,if_neg hi,realized θ p j,if_neg hj]
        omega
  · intro name hn
    rw [← keys] at hn
    obtain ⟨e,he,eq⟩ := List.mem_map.mp hn
    rw [← eq,lookup e he]
    exact ⟨bounds e he,atRank e he⟩

end LogicLineages.PermittedControl.ActualFiniteOrderBranches
