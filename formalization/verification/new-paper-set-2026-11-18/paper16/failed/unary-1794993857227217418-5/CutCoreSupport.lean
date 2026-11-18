import LogicLineages.PersistentMarking.CutCoreTargets
import LogicLineages.PersistentMarking.CutOccurrenceProof
import LogicLineages.PersistentMarking.CutOwnerProof
namespace LogicLineages.PersistentMarking.CutCoreSupport
open Spine ExtendedMeasure

theorem equivTrans {S : Signature} {f g h : Head} (a : Equivalent S f g) (b : Equivalent S g h) : Equivalent S f h := by
  obtain ⟨i,hf,hg⟩ := a; obtain ⟨j,hg',hh⟩ := b
  have he := Option.some.inj (hg.symm.trans hg'); subst j; exact ⟨i,hf,hh⟩
theorem precedeEquiv {S : Signature} {f g h : Head} (a : Precedes S f g) (b : Equivalent S g h) : Precedes S f h := by
  obtain ⟨i,j,hf,hg,hlt⟩ := a; obtain ⟨k,hg',hh⟩ := b
  have he := Option.some.inj (hg.symm.trans hg'); subst k; exact ⟨i,j,hf,hh,hlt⟩
theorem equivPrecede {S : Signature} {f g h : Head} (a : Equivalent S f g) (b : Precedes S g h) : Precedes S f h := by
  obtain ⟨i,hf,hg⟩ := a; obtain ⟨j,k,hg',hh,hlt⟩ := b
  have he := Option.some.inj (hg.symm.trans hg'); subst j; exact ⟨i,k,hf,hh,hlt⟩
theorem precedeTrans {S : Signature} {f g h : Head} (a : Precedes S f g) (b : Precedes S g h) : Precedes S f h := by
  obtain ⟨i,j,hf,hg,hlt⟩ := a; obtain ⟨k,l,hg',hh,hlt'⟩ := b
  have he := Option.some.inj (hg.symm.trans hg'); subst k; exact ⟨i,l,hf,hh,by omega⟩

theorem buildWhole (S : Signature) (f : Head) (base extras targets : Args)
    (hs : ∀ i q, At targets i q → ExtendedWeak S (.marked f q.type base extras) q) :
    _root_.Nonempty (ExtendedWholeTree S f base extras targets) := by
  cases targets with
  | nil => exact ⟨.wholeNil⟩
  | cons q qs =>
    obtain ⟨he⟩ := hs 0 q .here
    obtain ⟨ht⟩ := buildWhole S f base extras qs (fun i t ht => hs (i+1) t (.there ht))
    exact ⟨.wholeCons he ht⟩
termination_by sizeOf targets

theorem wholeMatching (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f : Head) (base extras middle targets : Args) (left : ExtendedWholeTree S f base extras middle)
    (right : ExtendedMatchingTree S middle targets) (hcount : treeSize right < n)
    (ho : OrdinaryArgs targets) : _root_.Nonempty (ExtendedWholeTree S f base extras targets) := by
  have hs : ∀ i q, At targets i q → ExtendedWeak S (.marked f q.type base extras) q := by
    intro i q hq
    obtain ⟨p,j,hp,edge,hbound⟩ := CutStrictWeakSupport.backAt right hq
    have he := CutOwnerProof.wholeAt left hp
    have ht := (ExtendedEndpointProof.weakFacts edge).2.2
    rw [ht] at he
    exact below _ p q edge (by omega) (CutStrictWeakSupport.ordinaryAt hq ho) he
  exact buildWhole S f base extras targets hs

theorem wholeRebase (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g : Head) (sb se tb te targets : Args) (ρ : Ty)
    (root : CutOwnerSyntax.Root S f sb se g tb te)
    (hp : PaperTerm S (.marked f ρ sb se) ρ) (ht : PaperTerm S (.marked g ρ tb te) ρ)
    (right : ExtendedWholeTree S g tb te targets) (hc : treeSize right < n)
    (ho : OrdinaryArgs targets) : _root_.Nonempty (ExtendedWholeTree S f sb se targets) := by
  cases targets with
  | nil => exact ⟨.wholeNil⟩
  | cons q qs =>
    cases right with
    | wholeCons edge rest =>
      have left := CutOwnerProof.retyped S f sb se g tb te q.type root
        (AuxiliaryReflexivityProof.retypePaper S f ρ q.type sb se hp)
        (AuxiliaryReflexivityProof.retypePaper S g ρ q.type tb te ht)
      have hb : treeSize edge < n := by change 1 + treeSize edge + treeSize rest < n at hc; omega
      have hr : treeSize rest < n := by change 1 + treeSize edge + treeSize rest < n at hc; omega
      obtain ⟨hout⟩ := below _ _ q edge hb ho.1 left
      obtain ⟨htail⟩ := wholeRebase S n below f g sb se tb te qs ρ root hp ht rest hr ho.2
      exact ⟨.wholeCons hout htail⟩
termination_by sizeOf targets
end LogicLineages.PersistentMarking.CutCoreSupport
