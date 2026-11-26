import LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverAlgorithmTargets
import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsAlgorithm

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverBoundsTargets
open NumberedWindowSyntax NumberedWindowPrimaryCoverSyntax NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode NumberedWindowHeadEnumerationTargets

def LiteralCoverBounds : Prop :=
  (∀ q : NTerm, (NumberedWindowCoverBoundsAlgorithm.bounds (encodeTerm q)).1 =
    ((termBounds q).nodes,(termBounds q).numeral)) ∧
  (∀ qs : NArgs, (NumberedWindowCoverBoundsAlgorithm.bounds (encodeArgs qs)).2 =
    ((argsBounds qs).nodes,(argsBounds qs).numeral))

def SourceSelectedCover : Prop := ∀ S K n,
  NumberedWindowCoverBoundsAlgorithm.cover ((admittedHeads S K).map encodeHead) (K.map encodeTy) n =
    (decodeTerm n).map (fun q => (cover S K q).map encodeTerm)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverBoundsTargets
