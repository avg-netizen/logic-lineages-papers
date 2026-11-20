import LogicLineages.PersistentMarking.NumberedWindowOwnerAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticOwnerTargets
open NumberedWindowOwnerAlgorithm NumberedWindowSyntax NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTyCode

def ExactOwnerCopies : Prop := ∀ f k bs es domains,
  copies (encodeHead f) k (encodeArgs bs) (encodeArgs es) (domains.map encodeTy) =
    encodeArgs (ownerCopies f k bs es domains)

def ExactArrowPrefix : Prop := ∀ domains result,
  (plan (encodeTy result) (domains.map encodeTy)).1 = encodeTy (Spine.ArrowPrefix domains result)

def ExactSelectedApplications : Prop := ∀ f k bs es domains result (q : NTerm),
  q.type = Spine.ArrowPrefix domains result →
    ∃ r, applications q (ownerCopies f k bs es domains) = some r ∧
      applyCopies (encodeHead f) k (encodeArgs bs) (encodeArgs es) (encodeTerm q)
        (plan (encodeTy result) (domains.map encodeTy)).2 = encodeTerm r ∧ r.type = result

end LogicLineages.PersistentMarking.NumberedWindowArithmeticOwnerTargets
