module
public import LogicLineages.PermittedControl.ActualFiniteOrderBranchesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteOrderBranches

private theorem choicesExact (k : Nat) (names : List Nat) (es : List Entry) :
    es ∈ choices k names ↔ es.map Prod.fst = names ∧ ∀ e ∈ es, e.2 < k := by
  induction names generalizing es with
  | nil =>
      cases es <;> simp [choices]
  | cons name names ih =>
      constructor
      · intro h
        obtain ⟨j,within,inMap⟩ := List.mem_flatMap.mp h
        obtain ⟨rest,hs,rfl⟩ := List.mem_map.mp inMap
        obtain ⟨shape,bounds⟩ := (ih rest).mp hs
        refine ⟨congrArg (List.cons name) shape,?_⟩
        intro e member
        rcases List.mem_cons.mp member with he | hm
        · subst e
          exact List.mem_range.mp within
        · exact bounds e hm
      · rintro ⟨shape,bounds⟩
        cases es with
        | nil => cases shape
        | cons e rest =>
            obtain ⟨same,tail⟩ := List.cons.inj shape
            have eq : e = (name,e.2) := Prod.ext same rfl
            have inTail : rest ∈ choices k names :=
              (ih rest).mpr ⟨tail,fun x hx => bounds x (List.mem_cons_of_mem _ hx)⟩
            exact List.mem_flatMap.mpr
              ⟨e.2,List.mem_range.mpr (bounds e List.mem_cons_self),
                List.mem_map.mpr ⟨rest,inTail,congrArg (fun x : Entry => x :: rest) eq.symm⟩⟩

private theorem ontoExact (k : Nat) (es : List Entry) :
    onto k es = true ↔ ∀ j : Nat, j < k → ∃ e ∈ es, e.2 = j := by
  simp only [onto,List.all_eq_true,List.mem_range,List.contains_iff_mem,List.mem_map]

theorem exactPatternEnumeration : ExactPatternEnumeration := by
  intro names p
  rcases p with ⟨k,es⟩
  constructor
  · intro h
    obtain ⟨i,within,inMap⟩ := List.mem_flatMap.mp h
    obtain ⟨vs,hv,eq⟩ := List.mem_map.mp inMap
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    obtain ⟨member,all⟩ := List.mem_filter.mp hv
    obtain ⟨namesEq,bounds⟩ := (choicesExact k names es).mp member
    exact ⟨Nat.le_of_lt_succ (List.mem_range.mp within),namesEq,bounds,(ontoExact k es).mp all⟩
  · rintro ⟨within,keys,bounds,all⟩
    refine List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (Nat.lt_succ_of_le within),?_⟩
    refine List.mem_map.mpr ⟨es,List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · exact (choicesExact k names es).mpr ⟨keys,bounds⟩
    · exact (ontoExact k es).mpr all

end LogicLineages.PermittedControl.ActualFiniteOrderBranches
