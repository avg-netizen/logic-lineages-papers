import LogicLineages.PersistentMarking.SharpSelectionProof
import LogicLineages.PersistentMarking.ExtendedOpeningProof
namespace LogicLineages.PersistentMarking.SharpResults
open Spine

/- Internal seven-sort motive for arbitrary targets. Ordered entries retain
actual extra/whole-owner suppliers and produce full Whole witnesses. -/
def Result (S : Signature) : ExtendedJudgment → Prop
  | .weak s t => ∀ q, RefinementTree S q s → ExtendedWeak S q t
  | .strict s t => ∀ q, RefinementTree S q s → ExtendedStrict S q t
  | .matching ss ts => ∀ qs, RefinementBasesTree S qs ss → _root_.Nonempty (ExtendedMatchingTree S qs ts)
  | .multiset ss ts => ∀ qs, RefinementBasesTree S qs ss → _root_.Nonempty (ExtendedMultisetTree S qs ts)
  | .coverage ss ts => ∀ qs, RefinementBasesTree S qs ss → _root_.Nonempty (ExtendedCoverageTree S qs ts)
  | .whole f base extras qs => ∀ qb qe τ,
      RefinementTree S (.marked f τ qb qe) (.marked f τ base extras) → _root_.Nonempty (ExtendedWholeTree S f qb qe qs)
  | .ordered ss ts => ∀ f base extras τ,
      PaperTerm S (.marked f τ base extras) τ → RefinementExtrasTree S f base extras ss →
      _root_.Nonempty (ExtendedWholeTree S f base extras ts)

def Smaller (S : Signature) (n : Nat) : Prop := ∀ j (h : ExtendedTree S j), ExtendedMeasure.treeSize h < n → Result S j
end LogicLineages.PersistentMarking.SharpResults
