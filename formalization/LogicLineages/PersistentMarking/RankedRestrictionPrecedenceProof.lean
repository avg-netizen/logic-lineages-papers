import LogicLineages.PersistentMarking.RankedRestrictionTargets

namespace LogicLineages.PersistentMarking.RankedRestrictionPrecedenceProof
open Spine RankedRestrictionTargets

private theorem lookupEntry (xs : List (Nat × Nat)) (name arity i : Nat)
    (h : lookupRank xs name = some (arity,i)) : xs[i]? = some (name,arity) := by
  induction xs generalizing i with
  | nil => cases h
  | cons a xs ih =>
    obtain ⟨n,b⟩ := a
    by_cases hn : name=n
    · subst n
      simp only [lookupRank,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      rfl
    · simp only [lookupRank,if_neg hn] at h
      cases he : lookupRank xs name with
      | none => simp [he] at h
      | some p =>
        obtain ⟨b',j⟩ := p
        simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ih j he

private theorem rankEntry (S : Signature) (name arity r : Nat)
    (h : classRank S (.ranked name arity) = some r) :
    ∃ i, S.entries[i]? = some (name,arity) ∧ r = i + 2 := by
  cases he : lookupRank S.entries name with
  | none => simp [classRank,he] at h
  | some p =>
    obtain ⟨b,i⟩ := p
    by_cases hb : arity=b
    · subst b
      exact ⟨i,lookupEntry S.entries name arity i he,by simpa [classRank,he] using h.symm⟩
    · simp [classRank,he,hb] at h

theorem sameHead (S : Signature) (f g : Head) (hf : RankedHead f) (hg : RankedHead g)
    (h : Equivalent S f g) : f=g := by
  cases f <;> try cases hf
  cases g <;> try cases hg
  rename_i n a m b
  obtain ⟨r,hF,hG⟩ := h
  obtain ⟨i,hi,hri⟩ := rankEntry S n a r hF
  obtain ⟨j,hj,hrj⟩ := rankEntry S m b r hG
  have he : i=j := by omega
  subst j
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (hi.symm.trans hj))
  rfl

end LogicLineages.PersistentMarking.RankedRestrictionPrecedenceProof
