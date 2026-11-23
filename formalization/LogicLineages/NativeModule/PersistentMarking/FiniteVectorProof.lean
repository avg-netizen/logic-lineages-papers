module

public import LogicLineages.NativeModule.PersistentMarking.FiniteDomainFoundationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.FiniteVectorProof
open FiniteDomainFoundation

theorem exactVector (bounds code : List Nat) : code ∈ vectors bounds ↔ Fits bounds code := by
  induction bounds generalizing code with
  | nil => cases code <;> simp [vectors,Fits]
  | cons n ns ih =>
    cases code with
    | nil => simp [vectors,Fits]
    | cons i is =>
      simp only [vectors,List.mem_flatMap,List.mem_map,List.mem_range]
      constructor
      · rintro ⟨j,hj,cs,hcs,he⟩
        cases he
        exact ⟨hj,(ih _).mp hcs⟩
      · rintro ⟨hi,his⟩
        exact ⟨i,hi,is,(ih _).mpr his,rfl⟩

theorem coordinates (bounds code : List Nat) : Fits bounds code ↔ bounds.length = code.length ∧
    ∀ (i n v : Nat), bounds[i]? = some n → code[i]? = some v → v<n := by
  induction bounds generalizing code with
  | nil => cases code <;> simp [Fits]
  | cons n ns ih =>
    cases code with
    | nil => simp [Fits]
    | cons v vs =>
      constructor
      · rintro ⟨hv,hrest⟩
        obtain ⟨hlen,hc⟩ := (ih vs).mp hrest
        refine ⟨by simp [hlen],?_⟩
        intro i a b ha hb
        cases i with
        | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at ha hb; subst a; subst b; exact hv
        | succ i => exact hc i a b ha hb
      · rintro ⟨hlen,hc⟩
        refine ⟨hc 0 n v rfl rfl,(ih vs).mpr ⟨?_,?_⟩⟩
        · simpa using hlen
        · intro i a b ha hb; exact hc (i+1) a b ha hb

/- Separate branches of the finite Cartesian enumeration have distinct
leading indices; multiplicities cannot become independent codes. -/
theorem distinct (bounds : List Nat) : (vectors bounds).Pairwise (· ≠ ·) := by
  induction bounds with
  | nil => exact .cons (by simp) .nil
  | cons n ns ih =>
    induction n with
    | zero => exact .nil
    | succ n ihn =>
      rw [vectors,List.range_succ,List.flatMap_append]
      apply List.pairwise_append.mpr
      refine ⟨ihn,?_,?_⟩
      · simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
        exact List.Pairwise.map _ (fun a b hab he => hab (List.cons.inj he).2) ih
      · intro a ha b hb he
        obtain ⟨i,hi,hxs⟩ := List.mem_flatMap.mp ha
        simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_map] at hb
        obtain ⟨ys,hys,rfl⟩ := hb
        obtain ⟨zs,hzs,hez⟩ := List.mem_map.mp hxs
        cases hez
        have hh := (List.cons.inj he).1
        have hi := List.mem_range.mp hi
        omega

theorem emptyZero : FiniteDomainFoundationTargets.EmptyAndZero :=
  ⟨rfl,fun _ => rfl⟩
end LogicLineages.PersistentMarking.FiniteVectorProof
