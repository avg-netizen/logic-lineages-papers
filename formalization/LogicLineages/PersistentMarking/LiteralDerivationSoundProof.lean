import LogicLineages.PersistentMarking.LiteralDerivationLocalityTargets

namespace LogicLineages.PersistentMarking.LiteralDerivationSoundProof
open Spine LiteralDerivationTree

def sound {S : Signature} {J : Judgment} : (tree : Tree S J) → Holds S J
  | .var _ _ => Weak.var
  | .abs _ _ _ _ _ hs ht hf hg t => Weak.abs hs ht hf hg (sound t)
  | .funHead _ _ _ _ hs ht he hTy ts => Weak.funHead hs ht he hTy (sound ts)
  | .put _ _ _ hs ht t => Weak.put hs ht (sound t)
  | .select _ _ _ _ _ _ _ _ _ hs ht hi hq hr t => Weak.select hs ht hi hq hr (sound t)
  | .fabs _ _ _ _ _ _ _ hs ht hf hg t => Weak.fabs hs ht hf hg (sound t)
  | .copy _ _ _ _ _ hs ht hp w => Weak.copy hs ht hp (sound w)
  | .stat _ _ _ _ _ hs ht he m w => Weak.stat hs ht he (sound m) (sound w)
  | .strictIntro _ _ _ _ hs ht hm t => Strict.intro hs ht hm (sound t)
  | .matchingNil => Matching.nil
  | .matchingCons _ _ _ _ _ h t more => Matching.cons h (sound t) (sound more)
  | .multisetReplace _ _ _ _ _ _ hs ht hn m c => Multiset.replace hs ht hn (sound m) (sound c)
  | .coverageNil _ => Coverage.nil
  | .coverageCons _ _ _ _ _ hi t more => Coverage.cons hi (sound t) (sound more)
  | .wholeNil _ _ _ => Whole.nil
  | .wholeCons _ _ _ _ _ t more => Whole.cons (sound t) (sound more)

end LogicLineages.PersistentMarking.LiteralDerivationSoundProof
