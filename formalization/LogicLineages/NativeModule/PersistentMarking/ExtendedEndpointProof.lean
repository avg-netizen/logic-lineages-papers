module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedComparison
public import LogicLineages.NativeModule.PersistentMarking.SpineShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedEndpointProof
open Spine

theorem facts {S : Signature} {q t : Expr} {σ : Ty}
    (hq : PaperTerm S q σ) (ht : PaperTerm S t σ) :
    PaperTerm S q q.type ∧ PaperTerm S t t.type ∧ q.type = t.type := by
  have hqτ := SpineShiftProof.annotationExact _ _ _ hq.1
  have htτ := SpineShiftProof.annotationExact _ _ _ ht.1
  exact ⟨hqτ.symm ▸ hq,htτ.symm ▸ ht,hqτ.trans htτ.symm⟩

theorem weakFacts {S : Signature} {q t : Expr} (h : ExtendedWeakTree S q t) :
    PaperTerm S q q.type ∧ PaperTerm S t t.type ∧ q.type = t.type := by
  cases h with
  | var => exact ⟨⟨.free,True.intro⟩,⟨.free,True.intro⟩,rfl⟩
  | abs hp ht _ _ _ => exact facts hp ht
  | funHead hp ht _ he _ => exact facts (he ▸ hp) ht
  | put hp ht _ => exact facts hp ht
  | select hp ht _ _ _ _ => exact facts hp ht
  | fabs hp ht _ _ _ => exact facts hp ht
  | copy hp ht _ _ => exact facts hp ht
  | stat hp ht _ _ _ => exact facts hp ht
  | inHead hp ht _ _ _ => exact facts hp ht
  | marked1 hp ht _ _ _ => exact facts hp ht
  | marked2 hp ht _ _ _ _ => exact facts hp ht
  | drop hp ht _ => exact facts hp ht
  | perm hp ht _ _ => exact facts hp ht
  | copies hp ht _ _ => exact facts hp ht
  | pselect hp ht _ _ _ _ _ => exact facts hp ht
end LogicLineages.PersistentMarking.ExtendedEndpointProof
