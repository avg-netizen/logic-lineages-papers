import LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverSyntax
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCode
import LogicLineages.PersistentMarking.NumberedWindowCoverAlgorithm

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverAlgorithmTargets
open Spine NumberedWindowSyntax NumberedWindowPrimaryCoverSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTyCode
open NumberedWindowHeadEnumerationTargets

def ExactPairedGrammar : Prop := ∀ (H : List Head) (K : List Ty) maxNumeral depth,
  NumberedWindowCoverAlgorithm.grammar (H.map encodeHead) (K.map encodeTy) maxNumeral depth =
    ((grammar H K maxNumeral depth).1.map encodeTerm, (grammar H K maxNumeral depth).2.map encodeArgs)

def ExactOriginalCover : Prop := ∀ S K (q : NTerm),
  (NumberedWindowCoverAlgorithm.grammar ((admittedHeads S K).map encodeHead) (K.map encodeTy)
    (termBounds q).numeral (termBounds q).nodes).1 = (cover S K q).map encodeTerm

end LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverAlgorithmTargets
