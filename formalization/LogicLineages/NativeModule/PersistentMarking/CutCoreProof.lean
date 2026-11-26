module

public import LogicLineages.NativeModule.PersistentMarking.CutCoreStep
public import LogicLineages.NativeModule.PersistentMarking.ConservativeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutCoreProof
open Spine ExtendedMeasure

/-- Secondary induction fixes this very right tree. -/
theorem leftInduction (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (t u : Expr) (right : ExtendedWeakTree S t u) (hc : treeSize right = n) (m : Nat) :
    ∀ s (left : ExtendedWeakTree S s t), treeSize left = m → Ordinary u → ExtendedWeak S s u :=
  Nat.strongRecOn (motive := fun m => ∀ s (left : ExtendedWeakTree S s t),
    treeSize left = m → Ordinary u → ExtendedWeak S s u) m
    (fun m ih s left he ho => step S n below s t u left right hc
      (fun s' left' hb ho' => ih (treeSize left') (by omega) s' left' rfl ho') ho)

/-- Primary induction admits arbitrary left witness sizes at smaller right count. -/
theorem rightInduction (S : Signature) (n : Nat) :
    ∀ t u (right : ExtendedWeakTree S t u), treeSize right = n →
      ∀ s, ExtendedWeak S s t → Ordinary u → ExtendedWeak S s u :=
  Nat.strongRecOn (motive := fun n => ∀ t u (right : ExtendedWeakTree S t u), treeSize right = n →
    ∀ s, ExtendedWeak S s t → Ordinary u → ExtendedWeak S s u) n
    (fun n ih t u right hc s hl ho => by
      have below : CutEdgeTargets.Below S n := fun a b c child hb ho' hl' =>
        ih (treeSize child) hb b c child rfl a hl' ho'
      obtain ⟨left⟩ := hl
      exact leftInduction S n below t u right hc (treeSize left) s left rfl ho)

theorem auxiliaryCut : CutCoreTargets.AuxiliaryCut := by
  intro S s t u hl hr ho
  obtain ⟨right⟩ := hr
  exact rightInduction S (treeSize right) t u right rfl s hl ho

theorem fullCut : CutCoreTargets.FullCut := by
  intro S s t u hl hr ho
  have hc := auxiliaryCut S s t u hl hr ho
  obtain ⟨left⟩ := hl
  have hp := (ExtendedEndpointProof.weakFacts left).1
  exact ConservativeProof.weak S s s u (AuxiliaryReflexivityProof.refinementRefl S s s.type hp) hc ho
end LogicLineages.PersistentMarking.CutCoreProof
