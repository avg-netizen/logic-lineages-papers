module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeSelectionProof
public import LogicLineages.NativeModule.PersistentMarking.ExtendedOpeningProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConservativeResults
open Spine

/- Internal seven-sort induction motive. Ordered premises only occur under
marked weak targets, which ordinary-target elimination excludes. -/
def Result (S : Signature) : ExtendedJudgment → Prop
  | .weak s t => ∀ q, RefinementTree S q s → Ordinary t → Weak S q t
  | .strict s t => ∀ q, RefinementTree S q s → Ordinary t → Strict S q t
  | .matching ss ts => ∀ qs, RefinementBasesTree S qs ss → OrdinaryArgs ts → Matching S qs ts
  | .multiset ss ts => ∀ qs, RefinementBasesTree S qs ss → OrdinaryArgs ts → Multiset S qs ts
  | .coverage ss ts => ∀ qs, RefinementBasesTree S qs ss → OrdinaryArgs ts → Coverage S qs ts
  | .whole f base extras qs => ∀ qb qe τ,
      RefinementTree S (.marked f τ qb qe) (.marked f τ base extras) → OrdinaryArgs qs → Whole S f qb qe qs
  | .ordered _ _ => True

def Smaller (S : Signature) (n : Nat) : Prop := ∀ j (h : ExtendedTree S j), ExtendedMeasure.treeSize h < n → Result S j
end LogicLineages.PersistentMarking.ConservativeResults
