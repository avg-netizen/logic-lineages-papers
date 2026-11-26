import LogicLineages.PersistentMarking.ExtendedComparison
namespace LogicLineages.PersistentMarking.ExtraCompressionTargets
open Spine

/-- Complete source extra-compression conclusion: both owners have the same
output type, literal base matching, and one retyped whole-owner comparison
for every target-extra occurrence. No cut/composition premise. -/
def ExtraCompression : Prop := ∀ S f g τ base extras targetBase targetExtras,
  PaperTerm S (.marked f τ base extras) τ →
  PaperTerm S (.marked g τ targetBase targetExtras) τ →
  Equivalent S f g →
  _root_.Nonempty (ExtendedMatchingTree S base targetBase) →
  _root_.Nonempty (ExtendedWholeTree S f base extras targetExtras) →
  ExtendedWeak S (.marked f τ base extras) (.marked g τ targetBase targetExtras)
end LogicLineages.PersistentMarking.ExtraCompressionTargets
