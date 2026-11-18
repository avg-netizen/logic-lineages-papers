module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceTieProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence
open HyperCloseBlock (existsNames)

def blockExists : List Nat → ((Nat → Nat) → Prop) → (Nat → Nat) → Prop
  | [],P,ν => P ν
  | x::xs,P,ν => ∃ n : Nat, blockExists xs P (Function.update ν x n)

theorem blockExists_names (xs : List Nat) (p : Matrix) (ν : Nat → Nat) :
    blockExists xs p.eval ν ↔ existsNames xs p ν := by
  induction xs generalizing ν with
  | nil => rfl
  | cons x xs ih => simp only [blockExists,existsNames,ih]

theorem blockExists_projection (xs : List Nat) (P : (Nat → Nat) → Prop) (ν : Nat → Nat) :
    blockExists xs P ν ↔ ∃ ρ : Nat → Nat, (∀ i, i ∉ xs → ρ i=ν i) ∧ P ρ := by
  induction xs generalizing ν with
  | nil =>
    constructor
    · intro h; exact ⟨ν,fun _ _ => rfl,h⟩
    · rintro ⟨ρ,he,hp⟩
      have hρ : ρ=ν := funext (fun i => he i (by simp))
      simpa [hρ,blockExists] using hp
  | cons x xs ih =>
    simp only [blockExists,ih]
    constructor
    · rintro ⟨n,ρ,he,hp⟩
      refine ⟨ρ,?_,hp⟩
      intro i hi
      have hn : i ∉ xs := by intro h; exact hi (List.mem_cons_of_mem x h)
      have hx : i ≠ x := by intro h; subst i; exact hi (by simp)
      rw [he i hn]
      simp [Function.update,hx]
    · rintro ⟨ρ,he,hp⟩
      refine ⟨ρ x,ρ,?_,hp⟩
      intro i hi
      by_cases hx : i=x
      · subst i; simp
      · rw [he i (by simp [hx,hi])]
        simp [Function.update,hx]


theorem names_projection (xs : List Nat) (p : Matrix) (ν : Nat → Nat) :
    existsNames xs p ν ↔ ∃ ρ : Nat → Nat, (∀ i, i ∉ xs → ρ i=ν i) ∧ p.eval ρ := by
  rw [← blockExists_names,blockExists_projection]

theorem names_mono (xs : List Nat) (p q : Matrix)
    (he : ∀ ν, p.eval ν → q.eval ν) (ν : Nat → Nat) :
    existsNames xs p ν → existsNames xs q ν := by
  rw [names_projection,names_projection]
  rintro ⟨ρ,ha,hp⟩
  exact ⟨ρ,ha,he ρ hp⟩

theorem live_nonempty (xs : List Nat) (p : NormalForm.Formula)
    (hx : xs ≠ []) (hi : inactive xs p=[]) : live xs p ≠ [] := by
  intro he
  have h : inactive xs p=xs := by simp [inactive,he]
  exact hx (h.symm.trans hi)

theorem fullCoverage : OrderedOccurrenceTargets.FullCoverage := by
  intro xs p hn ν
  by_cases hx : xs=[]
  · subst xs
    simp [dispatch,holds]
  by_cases hi : inactive xs p=[]
  · rw [dispatch,if_neg hx,if_pos hi]
    constructor
    · intro hp
      obtain ⟨ρ,ha,hp⟩ := (names_projection xs p.compile ν).mp hp
      rcases orderedCoverage xs hn ρ with ht | ⟨ys,hy,hs⟩
      · obtain ⟨i,hi',j,hj,hij,he⟩ := ht
        let o : Outcome := ⟨2,xs.erase i,i,j,p.compile.substitute i (.variable j)⟩
        refine ⟨o,List.mem_append_left _ ?_,?_⟩
        · apply List.mem_flatMap.mpr
          refine ⟨i,hi',List.mem_map.mpr ⟨j,?_,rfl⟩⟩
          simp [hj,hij.symm]
        · apply ((tieReduction xs p i j hn hi' hj hij).1 ν).mp
          exact (names_projection xs _ ν).mpr ⟨ρ,ha,he,hp⟩
      · obtain ⟨a,ham,hm⟩ := maximumCoverage xs p (live_nonempty xs p hx hi) ρ
        obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp ham
        let o : Outcome := ⟨3,ys,(summand a).name,k,
          .conjunction (strictOrder ys) (.conjunction (maximal xs p a) p.compile)⟩
        refine ⟨o,List.mem_append_right _ ?_,?_⟩
        · apply List.mem_flatMap.mpr
          exact ⟨ys,hy,List.mem_map.mpr ⟨(a,k),List.mk_mem_zipIdx_iff_getElem?.mpr hk,rfl⟩⟩
        · have hperm : ys.Perm xs := List.mem_permutations.mp hy
          apply (names_projection ys _ ν).mpr
          refine ⟨ρ,?_,hs,hm,hp⟩
          intro i hni
          exact ha i (fun h => hni (hperm.mem_iff.mpr h))
    · rintro ⟨o,ho,hh⟩
      rcases List.mem_append.mp ho with ht | ho
      · obtain ⟨i,hi',hj⟩ := List.mem_flatMap.mp ht
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hj
        have hj' : j∈xs ∧ j≠i := by simpa using hj
        have he := ((tieReduction xs p i j hn hi' hj'.1 hj'.2.symm).1 ν).mpr hh
        exact names_mono xs _ p.compile (fun _ h => h.2) ν he
      · obtain ⟨ys,hy,ho⟩ := List.mem_flatMap.mp ho
        obtain ⟨⟨a,k⟩,ha,rfl⟩ := List.mem_map.mp ho
        obtain ⟨ρ,he,hp⟩ := (names_projection ys _ ν).mp hh
        have hperm : ys.Perm xs := List.mem_permutations.mp hy
        apply (names_projection xs p.compile ν).mpr
        exact ⟨ρ,fun i hn => he i (fun h => hn (hperm.mem_iff.mp h)),hp.2.2⟩
  · rw [dispatch,if_neg hx,if_neg hi]
    constructor
    · intro hp
      obtain ⟨i,hi'⟩ := List.exists_mem_of_ne_nil hi
      exact ⟨⟨1,xs,i,0,p.compile⟩,List.mem_map.mpr ⟨i,hi',rfl⟩,hp⟩
    · rintro ⟨o,ho,hh⟩
      obtain ⟨i,hi',rfl⟩ := List.mem_map.mp ho
      exact hh
end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
