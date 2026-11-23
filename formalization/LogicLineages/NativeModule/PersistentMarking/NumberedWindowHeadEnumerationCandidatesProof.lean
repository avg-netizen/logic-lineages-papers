module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowHeadEnumerationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationCandidatesProof
open NumberedWindowDomain NumberedWindowHeadEnumerationTargets
open TypeSupport (subtypes)

private theorem subtypeSelf (τ : Ty) : τ ∈ subtypes τ := by
  cases τ <;> simp [subtypes]

private theorem subtypeLeft {ρ σ τ : Ty} (h : ρ ∈ subtypes σ) :
    ρ ∈ subtypes (.arrow σ τ) :=
  List.mem_cons_of_mem _ (List.mem_append_left _ h)

private theorem subtypeRight {ρ σ τ : Ty} (h : ρ ∈ subtypes τ) :
    ρ ∈ subtypes (.arrow σ τ) :=
  List.mem_cons_of_mem _ (List.mem_append_right _ h)

private theorem lookupHit (entries : List (Nat × Nat)) (name : Nat) {arity i : Nat}
    (h : Spine.lookupRank entries name = some (arity,i)) : (name,arity) ∈ entries := by
  induction entries generalizing arity i with
  | nil => simp [Spine.lookupRank] at h
  | cons entry xs ih =>
    obtain ⟨x,b⟩ := entry
    by_cases e : name = x
    · subst x
      have p : (b,0) = (arity,i) :=
        Option.some.inj (by simpa only [Spine.lookupRank,if_pos rfl,if_true] using h)
      have hb : b = arity := congrArg Prod.fst p
      subst arity
      exact List.mem_cons_self
    · cases ht : Spine.lookupRank xs name with
      | none => simp [Spine.lookupRank,e,ht] at h
      | some p =>
        rcases p with ⟨a,j⟩
        have hp : (a,j+1) = (arity,i) := Option.some.inj
          (by simpa only [Spine.lookupRank,if_neg e,ht,Option.map_some] using h)
        have ha : a = arity := congrArg Prod.fst hp
        subst arity
        exact List.mem_cons_of_mem _ (ih ht)

private theorem rankedEntry {S : Spine.Signature} {name arity : Nat}
    (h : Spine.Admitted S (.ranked name arity)) : (name,arity) ∈ S.entries := by
  obtain ⟨i,hi⟩ := h
  cases ht : Spine.lookupRank S.entries name with
  | none => simp [Spine.classRank,ht] at hi
  | some p =>
    rcases p with ⟨a,j⟩
    by_cases e : arity = a
    · subst arity
      exact lookupHit S.entries name ht
    · simp [Spine.classRank,ht,e] at hi

private theorem resultType {S K f ρ} (h : HeadInWindow S K f)
    (hρ : ρ ∈ subtypes f.result) : ρ ∈ K :=
  h.2 ρ (List.mem_append_left _ hρ)

private theorem argumentType {S K f σ} (h : HeadInWindow S K f)
    (hσ : σ ∈ f.arguments) : σ ∈ K :=
  h.2 σ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨σ,hσ,subtypeSelf σ⟩))

theorem candidate {S K f} (h : HeadInWindow S K f) : f ∈ candidates S K := by
  cases f with
  | zero => simp [candidates]
  | succ => simp [candidates]
  | case τ =>
    have hs : τ ∈ subtypes (.arrow .ground (.arrow τ (.arrow τ τ))) :=
      subtypeRight (σ := .ground) (subtypeLeft (τ := .arrow τ τ) (subtypeSelf τ))
    have hτ : τ ∈ K := resultType h hs
    have hm : Head.case τ ∈ K.map Head.case := List.mem_map_of_mem hτ
    simp only [candidates,List.mem_append,hm,true_or,or_true]
  | recursor τ =>
    have hs : τ ∈ subtypes (.arrow .ground
        (.arrow (.arrow .ground (.arrow τ τ)) (.arrow τ τ))) :=
      subtypeRight (σ := .ground)
        (subtypeRight (σ := .arrow .ground (.arrow τ τ)) (subtypeLeft (τ := τ) (subtypeSelf τ)))
    have hτ : τ ∈ K := resultType h hs
    have hm : Head.recursor τ ∈ K.map Head.recursor := List.mem_map_of_mem hτ
    simp only [candidates,List.mem_append,hm,true_or,or_true]
  | app σ τ =>
    have hσ : σ ∈ K := argumentType h (by simp [Head.arguments])
    have hτ : τ ∈ K := resultType h (subtypeSelf τ)
    have hm : Head.app σ τ ∈ K.flatMap (fun σ => K.map (Head.app σ)) :=
      List.mem_flatMap.mpr ⟨σ,hσ,List.mem_map_of_mem hτ⟩
    simp only [candidates,List.mem_append,hm,true_or,or_true]
  | ranked name arity =>
    have hm : Head.ranked name arity ∈ S.entries.map (fun p => Head.ranked p.1 p.2) :=
      List.mem_map.mpr ⟨(name,arity),rankedEntry h.1,rfl⟩
    simp only [candidates,List.mem_append,hm,true_or,or_true]

end LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationCandidatesProof
