module

public import LogicLineages.NativeModule.PersistentMarking.CutOwnerTargets
public import LogicLineages.NativeModule.PersistentMarking.TargetExtrasProof
public import LogicLineages.NativeModule.PersistentMarking.CutWeakStrictProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutOwnerProof
open Spine

theorem retyped : CutOwnerTargets.Retyped := by
  intro S f sb se g tb te τ root hp ht
  rcases root with ⟨heq,⟨hm⟩,⟨ho⟩⟩ | ⟨hprec,⟨hb⟩,⟨he⟩⟩ | ⟨heq,⟨hm⟩,⟨hb⟩,⟨he⟩⟩
  · exact ⟨.inHead hp ht heq hm ho⟩
  · exact ⟨.marked1 hp ht hprec hb he⟩
  · exact ⟨.marked2 hp ht heq hm hb he⟩

theorem wholePrefix : CutOwnerTargets.WholePrefix := by
  intro S f sb se g tb te ρ σ q root hp ht hcopy
  cases hcopy with
  | intro hprefix =>
    have hsource := AuxiliaryReflexivityProof.retypePaper S f ρ σ sb se hp
    have htarget := AuxiliaryReflexivityProof.retypePaper S g ρ σ tb te ht
    have he := retyped S f sb se g tb te σ root hsource htarget
    exact TargetExtrasProof.transform he (.prefix hprefix)

theorem orderedAt {S : Signature} {xs ys : Args} {i : Nat} {q : Expr}
    (h : ExtendedOrderedTree S xs ys) (ha : At ys i q) :
    ∃ p, At xs i p ∧ ExtendedWeak S p q := by
  induction ha generalizing xs with
  | here => cases h with | orderedCons edge rest => exact ⟨_,.here,⟨edge⟩⟩
  | there ha ih =>
    cases h with
    | orderedCons edge rest => obtain ⟨p,hp,he⟩ := ih rest; exact ⟨p,.there hp,he⟩

theorem wholeAt {S : Signature} {f : Head} {base extras targets : Args} {i : Nat} {q : Expr}
    (h : ExtendedWholeTree S f base extras targets) (ha : At targets i q) :
    ExtendedWeak S (.marked f q.type base extras) q := by
  induction ha with
  | here => cases h with | wholeCons edge rest => exact ⟨edge⟩
  | there ha ih => cases h with | wholeCons edge rest => exact ih rest

theorem selected : CutOwnerTargets.Selected := by
  intro S f sb se g tb te q i root ha
  rcases root with ⟨heq,⟨hm⟩,⟨ho⟩⟩ | ⟨hprec,⟨hb⟩,⟨he⟩⟩ | ⟨heq,⟨hm⟩,⟨hb⟩,⟨he⟩⟩
  · rcases ha with ha | ha
    · obtain ⟨p,j,hp,hpq⟩ := CutWeakStrictProof.matchingBackAt hm ha
      exact Or.inl ⟨p,j,Or.inl hp,hpq⟩
    · obtain ⟨p,hp,hpq⟩ := orderedAt ho ha
      exact Or.inl ⟨p,i,Or.inr hp,hpq⟩
  · exact Or.inr (ha.elim (wholeAt hb) (wholeAt he))
  · exact Or.inr (ha.elim (wholeAt hb) (wholeAt he))

theorem fullOwnerSuppliers : CutOwnerTargets.FullOwnerSuppliers := ⟨retyped,wholePrefix,selected⟩
end LogicLineages.PersistentMarking.CutOwnerProof
