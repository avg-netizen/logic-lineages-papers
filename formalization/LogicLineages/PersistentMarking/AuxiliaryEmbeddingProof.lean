import LogicLineages.PersistentMarking.AuxiliaryTargets
namespace LogicLineages.PersistentMarking.AuxiliaryEmbeddingProof
open Spine

theorem embedWeak (S : Signature) (q t : Expr) (h : Weak S q t) : ExtendedWeak S q t := by
  apply Weak.rec (motive_1 := fun q t _ => ExtendedWeak S q t)
    (motive_2 := fun q t _ => ExtendedStrict S q t)
    (motive_3 := fun xs ys _ => _root_.Nonempty (ExtendedMatchingTree S xs ys))
    (motive_4 := fun xs ys _ => _root_.Nonempty (ExtendedMultisetTree S xs ys))
    (motive_5 := fun xs ys _ => _root_.Nonempty (ExtendedCoverageTree S xs ys))
    (motive_6 := fun f bs es qs _ => _root_.Nonempty (ExtendedWholeTree S f bs es qs)) (t := h)
  · intro σ x; exact ⟨.var⟩
  · intro σ s τ t x hp hq hf hg hw ih
    obtain ⟨hw⟩ := ih
    exact ⟨.abs hp hq hf hg hw⟩
  · intro f ss g ts hp hq he ht hm ih
    obtain ⟨hm⟩ := ih
    exact ⟨.funHead hp hq he ht hm⟩
  · intro f ss t hp hq hw ih
    obtain ⟨hw⟩ := ih
    exact ⟨.put hp hq hw⟩
  · intro f τ ss es t i q domains r hp hq ho ht ha hw ih
    obtain ⟨hw⟩ := ih
    exact ⟨.select hp hq ho ht ha hw⟩
  · intro f σ τ ss es body x hp hq hf hg hw ih
    obtain ⟨hw⟩ := ih
    exact ⟨.fabs hp hq hf hg hw⟩
  · intro f ss es g ts hp hq hf hw ih
    obtain ⟨hw⟩ := ih
    exact ⟨.copy hp hq hf hw⟩
  · intro f ss es g ts hp hq hf hm hw ihm ihw
    obtain ⟨hm⟩ := ihm
    obtain ⟨hw⟩ := ihw
    exact ⟨.stat hp hq hf hm hw⟩
  · intro q σ t r hp hq hm hw ih
    obtain ⟨hw⟩ := ih
    exact ⟨.strictIntro hp hq hm hw⟩
  · exact ⟨.matchingNil⟩
  · intro targets y rest x xs hr hw hm ihw ihm
    obtain ⟨hw⟩ := ihw
    obtain ⟨hm⟩ := ihm
    exact ⟨.matchingCons hr hw hm⟩
  · intro source kept removed target matched added hs ht hn hm hc ihm ihc
    obtain ⟨hm⟩ := ihm
    obtain ⟨hc⟩ := ihc
    exact ⟨.multisetReplace hs ht hn hm hc⟩
  · intro owners; exact ⟨.coverageNil⟩
  · intro owners i q x xs ho hs hc ihs ihc
    obtain ⟨hs⟩ := ihs
    obtain ⟨hc⟩ := ihc
    exact ⟨.coverageCons ho hs hc⟩
  · intro f base extras; exact ⟨.wholeNil⟩
  · intro f base extras q qs hw hs ihw ihs
    obtain ⟨hw⟩ := ihw
    obtain ⟨hs⟩ := ihs
    exact ⟨.wholeCons hw hs⟩

theorem originalWeakEmbedding : AuxiliaryTargets.OriginalWeakEmbedding := embedWeak

theorem originalStrictEmbedding : AuxiliaryTargets.OriginalStrictEmbedding := by
  intro S q t h
  cases h with
  | intro hq ht hm hw =>
    obtain ⟨h⟩ := embedWeak S _ t hw
    exact ⟨.strictIntro hq ht hm h⟩
end LogicLineages.PersistentMarking.AuxiliaryEmbeddingProof
