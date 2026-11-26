import LogicLineages.PersistentMarking.LiteralDerivationBuilderProof

namespace LogicLineages.PersistentMarking.LiteralDerivationCompleteProof
open Spine LiteralDerivationTree LiteralDerivationBuilderProof

theorem complete (S : Signature) (J : Judgment) : Holds S J → Witness S J := by
  intro h
  cases J with
  | weak q t =>
    exact Weak.rec
      (motive_1 := fun q t _ => Witness S (.weak q t))
      (motive_2 := fun q t _ => Witness S (.strict q t))
      (motive_3 := fun xs ys _ => Witness S (.matching xs ys))
      (motive_4 := fun xs ys _ => Witness S (.multiset xs ys))
      (motive_5 := fun xs ys _ => Witness S (.coverage xs ys))
      (motive_6 := fun f bs es ts _ => Witness S (.whole f bs es ts))
      (BVar S) (BAbs S) (BFun S) (BPut S)
      (BSelect S) (BFAbs S) (BCopy S) (BStat S)
      (BStrict S) (BMatchNil S) (BMatchCons S) (BMultiset S)
      (BCoverNil S) (BCoverCons S) (BWholeNil S) (BWholeCons S)
      h
  | strict q t =>
    exact Strict.rec
      (motive_1 := fun q t _ => Witness S (.weak q t))
      (motive_2 := fun q t _ => Witness S (.strict q t))
      (motive_3 := fun xs ys _ => Witness S (.matching xs ys))
      (motive_4 := fun xs ys _ => Witness S (.multiset xs ys))
      (motive_5 := fun xs ys _ => Witness S (.coverage xs ys))
      (motive_6 := fun f bs es ts _ => Witness S (.whole f bs es ts))
      (BVar S) (BAbs S) (BFun S) (BPut S)
      (BSelect S) (BFAbs S) (BCopy S) (BStat S)
      (BStrict S) (BMatchNil S) (BMatchCons S) (BMultiset S)
      (BCoverNil S) (BCoverCons S) (BWholeNil S) (BWholeCons S)
      h
  | matching xs ys =>
    exact Matching.rec
      (motive_1 := fun q t _ => Witness S (.weak q t))
      (motive_2 := fun q t _ => Witness S (.strict q t))
      (motive_3 := fun xs ys _ => Witness S (.matching xs ys))
      (motive_4 := fun xs ys _ => Witness S (.multiset xs ys))
      (motive_5 := fun xs ys _ => Witness S (.coverage xs ys))
      (motive_6 := fun f bs es ts _ => Witness S (.whole f bs es ts))
      (BVar S) (BAbs S) (BFun S) (BPut S)
      (BSelect S) (BFAbs S) (BCopy S) (BStat S)
      (BStrict S) (BMatchNil S) (BMatchCons S) (BMultiset S)
      (BCoverNil S) (BCoverCons S) (BWholeNil S) (BWholeCons S)
      h
  | multiset xs ys =>
    exact Multiset.rec
      (motive_1 := fun q t _ => Witness S (.weak q t))
      (motive_2 := fun q t _ => Witness S (.strict q t))
      (motive_3 := fun xs ys _ => Witness S (.matching xs ys))
      (motive_4 := fun xs ys _ => Witness S (.multiset xs ys))
      (motive_5 := fun xs ys _ => Witness S (.coverage xs ys))
      (motive_6 := fun f bs es ts _ => Witness S (.whole f bs es ts))
      (BVar S) (BAbs S) (BFun S) (BPut S)
      (BSelect S) (BFAbs S) (BCopy S) (BStat S)
      (BStrict S) (BMatchNil S) (BMatchCons S) (BMultiset S)
      (BCoverNil S) (BCoverCons S) (BWholeNil S) (BWholeCons S)
      h
  | coverage xs ys =>
    exact Coverage.rec
      (motive_1 := fun q t _ => Witness S (.weak q t))
      (motive_2 := fun q t _ => Witness S (.strict q t))
      (motive_3 := fun xs ys _ => Witness S (.matching xs ys))
      (motive_4 := fun xs ys _ => Witness S (.multiset xs ys))
      (motive_5 := fun xs ys _ => Witness S (.coverage xs ys))
      (motive_6 := fun f bs es ts _ => Witness S (.whole f bs es ts))
      (BVar S) (BAbs S) (BFun S) (BPut S)
      (BSelect S) (BFAbs S) (BCopy S) (BStat S)
      (BStrict S) (BMatchNil S) (BMatchCons S) (BMultiset S)
      (BCoverNil S) (BCoverCons S) (BWholeNil S) (BWholeCons S)
      h
  | whole f bs es ts =>
    exact Whole.rec
      (motive_1 := fun q t _ => Witness S (.weak q t))
      (motive_2 := fun q t _ => Witness S (.strict q t))
      (motive_3 := fun xs ys _ => Witness S (.matching xs ys))
      (motive_4 := fun xs ys _ => Witness S (.multiset xs ys))
      (motive_5 := fun xs ys _ => Witness S (.coverage xs ys))
      (motive_6 := fun f bs es ts _ => Witness S (.whole f bs es ts))
      (BVar S) (BAbs S) (BFun S) (BPut S)
      (BSelect S) (BFAbs S) (BCopy S) (BStat S)
      (BStrict S) (BMatchNil S) (BMatchCons S) (BMultiset S)
      (BCoverNil S) (BCoverCons S) (BWholeNil S) (BWholeCons S)
      h

end LogicLineages.PersistentMarking.LiteralDerivationCompleteProof
