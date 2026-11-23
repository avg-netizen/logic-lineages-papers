module

public import LogicLineages.NativeModule.PersistentMarking.TargetExtrasStep

@[expose] public section

namespace LogicLineages.PersistentMarking.TargetExtrasProof
open Spine TargetExtrasResults TargetExtrasRootSupport ExtendedMeasure

theorem prove (S : Signature) (n : Nat) : ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j :=
  Nat.strongRecOn (motive := fun n => ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j) n
    (fun n ih j h hn => step S n (fun j' h' hlt => ih (treeSize h') hlt j' h' rfl) j h hn)

theorem transform {S : Signature} {s : Expr} {f : Head} {τ : Ty} {base extras changed : Args}
    (h : ExtendedWeak S s (.marked f τ base extras)) (hc : Change f base extras changed) :
    ExtendedWeak S s (.marked f τ base changed) := by
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl f τ base extras rfl changed hc

theorem suffixRemoval : TargetExtrasTargets.SuffixRemoval := by
  intro S s f τ base extras suffix h
  exact transform h (.prefix (ConservativeOwnerSupport.prefixAppend extras suffix))

theorem targetPermutation : TargetExtrasTargets.TargetPermutation := by
  intro S s f τ base extras reordered h hp
  exact transform h (.perm hp)

theorem copyAddition : TargetExtrasTargets.CopyAddition := by
  intro S s f τ base extras copies h hc
  exact transform h (.copies hc)

theorem fullTargetExtras : TargetExtrasTargets.FullTargetExtras :=
  ⟨suffixRemoval,targetPermutation,copyAddition⟩
end LogicLineages.PersistentMarking.TargetExtrasProof
